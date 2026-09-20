import Construction.Simulator.OnlineInput
import Proof.Privacy.Simulator.Arithmetic.QueryInputBlock
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The reader contains all five fixed input blocks. -/
theorem onlineInput_blocks :
    ContainsWordInput onlineInput 254 (onlineInputLabels 0 14) ∧
    ContainsWordInput onlineInput 254 (onlineInputLabels 17 31) ∧
    ContainsWordInput onlineInput 2 (onlineInputLabels 34 48) ∧
    ContainsWordInput onlineInput 254 (onlineInputLabels 54 68) ∧
    ContainsWordInput onlineInput 254 (onlineInputLabels 71 85) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro pc inside
    have guard0 : 0 + pc.val < 14 := by omega
    simp [onlineInput, onlineInputLabels, inside, guard0]
  · intro pc inside
    have guard0 : ¬ (17 + pc.val < 14) := by omega
    have guard1 : 17 ≤ 17 + pc.val ∧ 17 + pc.val < 31 := by omega
    simp [onlineInput, onlineInputLabels, inside, guard0, guard1]
  · intro pc inside
    have guard0 : ¬ (34 + pc.val < 14) := by omega
    have guard1 : ¬ (17 ≤ 34 + pc.val ∧ 34 + pc.val < 31) := by omega
    have guard2 : 34 ≤ 34 + pc.val ∧ 34 + pc.val < 48 := by omega
    simp [onlineInput, onlineInputLabels, inside, guard0, guard1, guard2]
  · intro pc inside
    have guard0 : ¬ (54 + pc.val < 14) := by omega
    have guard1 : ¬ (17 ≤ 54 + pc.val ∧ 54 + pc.val < 31) := by omega
    have guard2 : ¬ (34 ≤ 54 + pc.val ∧ 54 + pc.val < 48) := by omega
    have guard3 : 54 ≤ 54 + pc.val ∧ 54 + pc.val < 68 := by omega
    simp [onlineInput, onlineInputLabels, inside, guard0, guard1, guard2, guard3]
  · intro pc inside
    have guard0 : ¬ (71 + pc.val < 14) := by omega
    have guard1 : ¬ (17 ≤ 71 + pc.val ∧ 71 + pc.val < 31) := by omega
    have guard2 : ¬ (34 ≤ 71 + pc.val ∧ 71 + pc.val < 48) := by omega
    have guard3 : ¬ (54 ≤ 71 + pc.val ∧ 71 + pc.val < 68) := by omega
    have guard4 : 71 ≤ 71 + pc.val ∧ 71 + pc.val < 85 := by omega
    simp [onlineInput, onlineInputLabels, inside, guard0, guard1, guard2, guard3, guard4]

/-- Each store has three instruction labels and one return label. -/
def onlineStoreLabels (start : Fin 96) (returnLabel : Fin 98) (index : Nat) : Fin 98 :=
  if inside : index < 3 then ⟨start.val + index, by have := start.isLt; omega⟩ else returnLabel

/-- The online reader contains all five RAM stores. -/
theorem onlineInput_stores :
    ContainsLinear onlineInput (onlineInputStore 0) (onlineStoreLabels 14 17) ∧
    ContainsLinear onlineInput (onlineInputStore 1) (onlineStoreLabels 31 34) ∧
    ContainsLinear onlineInput (onlineInputStore 2) (onlineStoreLabels 48 51) ∧
    ContainsLinear onlineInput (onlineInputStore 3) (onlineStoreLabels 68 71) ∧
    ContainsLinear onlineInput (onlineInputStore 4) (onlineStoreLabels 85 97) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro index valid <;>
    have small : index < 3 := valid
  all_goals interval_cases index <;>
    simp [onlineInput, onlineInputStore, onlineStoreLabels, LinearInstruction.emit]

/-- The store changes one RAM cell and two address registers. -/
def onlineStored (offset : Word) (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update memory.registers 15 offset) 8
      (memory.registers 10 + offset)
    ram := Function.update memory.ram (memory.registers 10 + offset) (memory.registers 0) }

theorem onlineInputStore_memory (offset : Word) (memory : Memory) :
    executeLinear (onlineInputStore offset) memory = onlineStored offset memory := by
  simp [executeLinear, onlineInputStore, LinearInstruction.execute, Arithmetic.eval, onlineStored]

/-- The output branch preserves its parsed tag and tests whether coordinates follow. -/
def onlineBranchMemory (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update memory.registers 15 1) 6 (memory.registers 0 - 1) }

theorem onlineInput_branch [BN254.FieldCertificate] (memory : Memory) :
    runPrefix onlineInput 3 ⟨51, memory⟩ =
      PMF.pure (some (false, ⟨if memory.registers 0 = 1 then 54 else 90,
        onlineBranchMemory memory⟩, 3)) := by
  by_cases affine : memory.registers 0 = 1 <;>
    simp [runPrefix, step, onlineInput, Arithmetic.eval, onlineBranchMemory, affine, BitVec.sub_eq_iff_eq_add, PMF.pure_map]
  all_goals rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
