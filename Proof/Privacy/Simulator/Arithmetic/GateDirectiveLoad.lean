import Construction.Simulator.GateDirectiveLoad
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSegment

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The selector returns the exact selected coordinate bit. -/
theorem gateBitSelect_value (index : Fin 508) (base : Memory) :
    (executeLinear (gateBitSelect index) base).registers 1 = selectedBitWord index base := by
  have fits : selectedBit index < 2 ^ 256 := lt_trans (selectedBit_bound index) (by decide)
  have word : (BitVec.ofNat 256 (selectedBit index)).toNat = selectedBit index := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  simp [gateBitSelect, executeLinear, LinearInstruction.execute, Arithmetic.eval, selectedBitWord, word]

/-- The selector preserves RAM, stacks, and caller registers. -/
theorem gateBitSelect_preserves (index : Fin 508) (base : Memory) :
    let result := executeLinear (gateBitSelect index) base
    result.ram = base.ram ∧ result.bits = base.bits ∧
      ∀ register : Register, 11 ≤ register.val → result.registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 11) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gateBitSelect, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 3 (by decide))]

/-- The label reader returns the selected label and saves the coordinate bit. -/
theorem gateLabelRead_values (index : Fin 508) (base : Memory) :
    let result := executeLinear (gateLabelRead index) base
    result.registers 9 = base.ram (base.registers 14 + BitVec.ofNat 256 index.val) ∧
    result.registers 10 = base.registers 1 := by
  simp [gateLabelRead, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The label reader preserves RAM, stacks, and caller registers. -/
theorem gateLabelRead_preserves (index : Fin 508) (base : Memory) :
    let result := executeLinear (gateLabelRead index) base
    result.ram = base.ram ∧ result.bits = base.bits ∧
      ∀ register : Register, 11 ≤ register.val → result.registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 11) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gateLabelRead, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 3 (by decide)),
    Function.update_of_ne (different 9 (by decide)), Function.update_of_ne (different 10 (by decide))]

/-- The data reader returns the exact three private source words. -/
theorem gateDataRead_values (target quotient table : Nat) (base : Memory) :
    let result := executeLinear (gateDataRead target quotient table) base
    result.registers 0 = base.ram (base.registers 11 + BitVec.ofNat 256 target) ∧
    result.registers 1 = base.ram (base.registers 11 + BitVec.ofNat 256 quotient) ∧
    result.registers 8 = base.ram (base.registers 11 + BitVec.ofNat 256 table) := by
  simp [gateDataRead, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The data reader preserves all registers from nine through fifteen. -/
theorem gateDataRead_preserves (target quotient table : Nat) (base : Memory) :
    let result := executeLinear (gateDataRead target quotient table) base
    result.ram = base.ram ∧ result.bits = base.bits ∧
      ∀ register : Register, 9 ≤ register.val → result.registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gateDataRead, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 8 (by decide))]

/-- The complete loader returns the exact gate input words. -/
theorem gateDirectiveLoad_values (index : Fin 508) (target quotient table : Nat) (base : Memory) :
    let result := executeLinear (gateDirectiveLoad index target quotient table) base
    result.registers 0 = base.ram (base.registers 11 + BitVec.ofNat 256 target) ∧
    result.registers 1 = base.ram (base.registers 11 + BitVec.ofNat 256 quotient) ∧
    result.registers 8 = base.ram (base.registers 11 + BitVec.ofNat 256 table) ∧
    result.registers 9 = base.ram (base.registers 14 + BitVec.ofNat 256 index.val) ∧
    result.registers 10 = selectedBitWord index base := by
  simp only [gateDirectiveLoad, executeLinear_append]
  have bits := gateBitSelect_preserves index base
  have labels := gateLabelRead_preserves index (executeLinear (gateBitSelect index) base)
  have data := gateDataRead_values target quotient table
    (executeLinear (gateLabelRead index) (executeLinear (gateBitSelect index) base))
  simp only [labels.1, bits.1, labels.2.2 11 (by decide), bits.2.2 11 (by decide)] at data
  refine ⟨data.1, data.2.1, data.2.2, ?_, ?_⟩
  · rw [(gateDataRead_preserves target quotient table _).2.2 9 (by decide),
      (gateLabelRead_values index _).1, bits.1, bits.2.2 14 (by decide)]
  · rw [(gateDataRead_preserves target quotient table _).2.2 10 (by decide),
      (gateLabelRead_values index _).2, gateBitSelect_value]

/-- The complete loader preserves RAM, stacks, and caller pointers. -/
theorem gateDirectiveLoad_preserves (index : Fin 508) (target quotient table : Nat) (base : Memory) :
    let result := executeLinear (gateDirectiveLoad index target quotient table) base
    result.ram = base.ram ∧ result.bits = base.bits ∧
      ∀ register : Register, 11 ≤ register.val → result.registers register = base.registers register := by
  simp only [gateDirectiveLoad, executeLinear_append]
  have first := gateBitSelect_preserves index base
  have second := gateLabelRead_preserves index (executeLinear (gateBitSelect index) base)
  have third := gateDataRead_preserves target quotient table
    (executeLinear (gateLabelRead index) (executeLinear (gateBitSelect index) base))
  refine ⟨third.1.trans (second.1.trans first.1), third.2.1.trans (second.2.1.trans first.2.1), ?_⟩
  intro register caller
  rw [third.2.2 register (by omega), second.2.2 register caller, first.2.2 register caller]

/-- The complete loader uses twenty-one fixed instructions. -/
theorem gateDirectiveLoad_length (index : Fin 508) (target quotient table : Nat) :
    (gateDirectiveLoad index target quotient table).length = 21 := by
  simp [gateDirectiveLoad, gateBitSelect, gateLabelRead, gateDataRead]

/-- The host loader returns after its exact instruction charge. -/
theorem gateDirectiveLoadHost_continue [BN254.FieldCertificate] (host : Machine)
    (index : Fin 508) (target quotient table : Nat) (labels : Nat → Fin (host.size + 1))
    (present : ContainsLinear host (gateDirectiveLoad index target quotient table) labels)
    (base : Memory) (fuel : Nat) :
    run host (21 + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 21, executeLinear (gateDirectiveLoad index target quotient table) base⟩).map
        (Option.map fun result => (result.1, result.2 + 21)) := by
  simpa only [gateDirectiveLoad_length] using
    linear_continue host (gateDirectiveLoad index target quotient table) labels present base fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
