import Construction.Simulator.SelectedLabels
import Proof.Privacy.Simulator.Arithmetic.ByteOutput
import Proof.Privacy.Simulator.Arithmetic.HashOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The selector mask gives exactly the selected coordinate bit. -/
def selectedBitWord (index : Fin 508) (base : Memory) : Word :=
  (base.ram (base.registers 12 + BitVec.ofNat 256 (selectedCoordinate index)) >>> selectedBit index) &&& 1

/-- The selector reads the false label or the preceding true label. -/
def selectedLabelWord (index : Fin 508) (base : Memory) : Word :=
  base.ram (base.registers 11 + (BitVec.ofNat 256 (selectedFalseOffset index) - selectedBitWord index base))

/-- Every selected coordinate bit lies below 254. -/
theorem selectedBit_bound (index : Fin 508) : selectedBit index < 254 := by
  unfold selectedBit
  split <;> have bound := index.isLt <;> omega

/-- The fixed selector instructions return the exact selected RAM word. -/
theorem labelSelect_word (index : Fin 508) (base : Memory) :
    (executeLinear (labelSelect index) base).registers 8 = selectedLabelWord index base := by
  have fits : selectedBit index < 2 ^ 256 := lt_trans (selectedBit_bound index) (by decide)
  have word : (BitVec.ofNat 256 (selectedBit index)).toNat = selectedBit index := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  simp only [labelSelect, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_self, Function.update_of_ne (by decide : (12 : Register) ≠ 0),
    Function.update_of_ne (by decide : (1 : Register) ≠ 2), Function.update_of_ne (by decide : (1 : Register) ≠ 3),
    Function.update_of_ne (by decide : (11 : Register) ≠ 0), Arithmetic.eval]
  simp [word, selectedLabelWord, selectedBitWord]

/-- Label selection preserves RAM and every bit stack. -/
theorem labelSelect_data (index : Fin 508) (base : Memory) :
    (executeLinear (labelSelect index) base).ram = base.ram ∧
    (executeLinear (labelSelect index) base).bits = base.bits := by
  simp [labelSelect, executeLinear, LinearInstruction.execute]

/-- Label selection preserves every caller register from eleven through fifteen. -/
theorem labelSelect_caller (index : Fin 508) (base : Memory) (register : Register) (caller : 11 ≤ register.val) :
    (executeLinear (labelSelect index) base).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 11) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [labelSelect, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 8 (by decide)), Function.update_of_ne (different 0 (by decide)),
    Function.update_of_ne (different 1 (by decide)), Function.update_of_ne (different 2 (by decide)),
    Function.update_of_ne (different 3 (by decide))]

/-- Each emitted label segment has 395 fixed instructions. -/
theorem selectedLabelSegment_length (index : Fin 508) : (selectedLabelSegment index).length = 395 := by
  simp [selectedLabelSegment, labelSelect, wordOutput_length]

/-- Every label segment emits exactly its selected 128-bit wire value. -/
theorem selectedLabelSegment_bits (index : Fin 508) (base : Memory) :
    (executeLinear (selectedLabelSegment index) base).bits = Function.update base.bits 3
      (GarbledCircuit.SimulatorProtocol.bits 128 (selectedLabelWord index base).toNat ++ base.bits 3) := by
  rw [selectedLabelSegment, executeLinear_append]
  rw [wordOutput_bits 128 _ (by decide), wordOutput_protocol, labelSelect_word, (labelSelect_data index base).2]

/-- Every label segment preserves its RAM source. -/
theorem selectedLabelSegment_ram (index : Fin 508) (base : Memory) :
    (executeLinear (selectedLabelSegment index) base).ram = base.ram := by
  rw [selectedLabelSegment, executeLinear_append]
  rw [wordOutput_ram, (labelSelect_data index base).1]

/-- Every label segment preserves all source pointers. -/
theorem selectedLabelSegment_caller (index : Fin 508) (base : Memory) (register : Register) (caller : 11 ≤ register.val) :
    (executeLinear (selectedLabelSegment index) base).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 11) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  rw [selectedLabelSegment, executeLinear_append]
  rw [wordOutput_saved _ _ register (different 9 (by decide)) (different 10 (by decide)), labelSelect_caller index base register caller]

end Kriterion.ArgoMAC.ArithmeticSimulator
