import Construction.Simulator.WordOutput
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The output program has three instructions per bit. -/
theorem wordOutput_length (width : Nat) : (wordOutput width).length = 3 * width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [wordOutput, ih]; omega

/-- The output block preserves its source register. -/
theorem wordOutput_source (width : Nat) (memory : Memory) :
    (executeLinear (wordOutput width) memory).registers 8 = memory.registers 8 := by
  induction width generalizing memory with
  | zero => rfl
  | succ width ih =>
      simp only [wordOutput, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput width) _).registers 8 = memory.registers 8
      rw [ih]
      simp [LinearInstruction.execute]

/-- The output block preserves RAM. -/
theorem wordOutput_ram (width : Nat) (memory : Memory) :
    (executeLinear (wordOutput width) memory).ram = memory.ram := by
  induction width generalizing memory with
  | zero => rfl
  | succ width ih =>
      simp only [wordOutput, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput width) _).ram = memory.ram
      rw [ih]
      rfl

/-- The output stack contains the low bits first and retains its previous suffix. -/
theorem wordOutput_bits (width : Nat) (memory : Memory) (fits : width ≤ 256) :
    (executeLinear (wordOutput width) memory).bits =
      Function.update memory.bits 3
        ((List.range width).map (memory.registers 8).getLsbD ++ memory.bits 3) := by
  induction width generalizing memory with
  | zero => simp [wordOutput, executeLinear, Function.update_eq_self]
  | succ width ih =>
      have small : width < 2 ^ 256 := lt_of_lt_of_le (by omega : width < 256) (by decide)
      norm_num at small
      simp only [wordOutput, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput width) _).bits = _
      rw [ih _ (by omega)]
      simp [LinearInstruction.execute, Arithmetic.eval, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt small, List.range_succ, List.map_append, List.append_assoc,
        BitVec.getLsbD_ushiftRight]

/-- The output bits use the challenge's canonical wire format. -/
theorem wordOutput_protocol (width : Nat) (value : Word) :
    (List.range width).map value.getLsbD =
      GarbledCircuit.SimulatorProtocol.bits width value.toNat := by
  apply List.ext_getElem
  · simp [GarbledCircuit.SimulatorProtocol.bits]
  · intro index left right
    have bound : index < width := by simpa using left
    simp [GarbledCircuit.SimulatorProtocol.bits, BitVec.getLsb, BitVec.getLsbD,
      Nat.testBit_mod_two_pow, bound]

/-- Every supported output width fits the machine address space. -/
theorem wordOutput_fits (width : Nat) (fits : width ≤ 256) :
    (wordOutput width).length < 2 ^ 256 := by
  rw [wordOutput_length]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 3 fits) (by decide)

/-- A compiled word output returns the canonical stack and exact executed cost. -/
theorem wordOutput_machine [BN254.FieldCertificate] (width : Nat) (memory : Memory)
    (fits : width ≤ 256) :
    let machine := linearMachine (wordOutput width) (wordOutput_fits width fits)
    (run machine (3 * width + 1) ⟨⟨0, by simp [machine, linearMachine]⟩, memory⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.2)) =
      PMF.pure (some (GarbledCircuit.SimulatorProtocol.bits width (memory.registers 8).toNat ++
        memory.bits 3, 3 * width + 1)) := by
  dsimp only
  rw [← wordOutput_length width, linearMachine_run, PMF.pure_map]
  simp [wordOutput_bits width memory fits, wordOutput_protocol, wordOutput_length]

/-- The complete charge includes the emitted program table and the executed instructions. -/
theorem wordOutput_budget (width : Nat) :
    (wordOutput width).length + 1 + (3 * width + 1) = 6 * width + 2 := by
  rw [wordOutput_length]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
