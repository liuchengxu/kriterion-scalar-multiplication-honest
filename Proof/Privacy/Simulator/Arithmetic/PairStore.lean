import Construction.Simulator.PairStore
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The five fixed instructions have exactly the pair-store memory effect. -/
theorem pairStore_memory (memory : Memory) :
    executeLinear pairStore memory = pairStored memory := by
  simp [executeLinear, pairStore, LinearInstruction.execute, Arithmetic.eval, pairStored,
    Function.update_eq_self, Function.update_comm]

/-- Consecutive RAM addresses differ even when the word address wraps. -/
theorem pairAddress_ne (address : Word) : address + 1#256 ≠ address := by
  intro equal
  have values := congrArg BitVec.toNat equal
  have bound := address.isLt
  simp only [BitVec.toNat_add] at values
  norm_num at values bound
  omega

/-- The store preserves both values, including at the last word address. -/
theorem pairStored_values (memory : Memory) :
    (pairStored memory).ram (memory.registers 9) = memory.registers 8 ∧
      (pairStored memory).ram (memory.registers 9 + 1#256) = memory.registers 10 := by
  simp [pairStored, Function.update_of_ne (Ne.symm (pairAddress_ne (memory.registers 9)))]

/-- The store leaves all other RAM cells unchanged. -/
theorem pairStored_other (memory : Memory) (address : Word)
    (first : address ≠ memory.registers 9)
    (second : address ≠ memory.registers 9 + 1#256) :
    (pairStored memory).ram address = memory.ram address := by
  simp [pairStored, first, second]

/-- The host returns from the pair store after exactly five instructions. -/
theorem pairStore_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host pairStore labels)
    (memory : Memory) (fuel : Nat) :
    run host (5 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 5, pairStored memory⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  have length : pairStore.length = 5 := rfl
  simpa only [pairStore_memory, length] using linear_continue host pairStore labels present memory fuel

/-- The standalone pair store includes six table entries and six executed instructions. -/
theorem pairStore_budget : pairStore.length + 1 + (pairStore.length + 1) = 12 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
