import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The dispatcher changes only its two temporary registers. -/
def publicDispatchMemory (memory : Memory) : Memory :=
  if memory.registers 10 = 4#256 then
    { memory with registers := Function.update (Function.update memory.registers 14 4) 13 0 }
  else
    { memory with registers := (Function.update (Function.update memory.registers 14 1)
      13 (memory.registers 10 &&& 1#256)) }

/-- The query tag selects one of the three public handlers. -/
def publicDispatchLabel (memory : Memory) : Fin 1772 :=
  if memory.registers 10 = 4#256 then 542
  else if memory.registers 10 &&& 1#256 = 0#256 then 102 else 299

/-- The hash branch uses three instructions and each permutation branch uses six. -/
def publicDispatchCost (memory : Memory) : Nat := if memory.registers 10 = 4#256 then 3 else 6

/-- The host contains the six fixed dispatcher instructions. -/
def ContainsPublicDispatch (host : Machine) (labels : Fin 9 → Fin (host.size + 1)) : Prop :=
  host.code[(labels 0).val] = .constant 14 4 (labels 1) ∧
  host.code[(labels 1).val] = .arithmetic .xor 13 10 14 (labels 2) ∧
  host.code[(labels 2).val] = .branch 13 (labels 6) (labels 3) ∧
  host.code[(labels 3).val] = .constant 14 1 (labels 4) ∧
  host.code[(labels 4).val] = .arithmetic .and 13 10 14 (labels 5) ∧
  host.code[(labels 5).val] = .branch 13 (labels 7) (labels 8)

/-- The host dispatcher preserves the exact source memory and cost. -/
theorem publicDispatchHost [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 9 → Fin (host.size + 1)) (present : ContainsPublicDispatch host labels)
    (memory : Memory) :
    runPrefix host (publicDispatchCost memory) ⟨labels 0, memory⟩ =
      PMF.pure (some (false,
        ⟨if memory.registers 10 = 4#256 then labels 6
          else if memory.registers 10 &&& 1#256 = 0#256 then labels 7 else labels 8,
          publicDispatchMemory memory⟩, publicDispatchCost memory)) := by
  rcases present with ⟨c0, c1, c2, c3, c4, c5⟩
  by_cases hash : memory.registers 10 = 4#256
  · simp [publicDispatchCost, publicDispatchMemory, hash,
      runPrefix, step, c0, c1, c2, Arithmetic.eval, PMF.pure_map]
  · by_cases even : memory.registers 10 &&& 1#256 = 0#256
    · simp [publicDispatchCost, publicDispatchMemory, hash, even,
        runPrefix, step, c0, c1, c2, c3, c4, c5, Arithmetic.eval, PMF.pure_map, Function.update_comm]
    · simp [publicDispatchCost, publicDispatchMemory, hash, even,
        runPrefix, step, c0, c1, c2, c3, c4, c5, Arithmetic.eval, PMF.pure_map, Function.update_comm]

/-- The first six labels hold the dispatcher and the last three select its handlers. -/
def publicDispatchLabels (index : Fin 9) : Fin 1772 :=
  if inside : index.val < 6 then ⟨96 + index.val, by omega⟩
  else if index = 6 then 542 else if index = 7 then 102 else 299

/-- The public table contains all six fixed dispatcher instructions. -/
theorem publicHandler_containsDispatch (attempts : Nat) :
    ContainsPublicDispatch (publicHandler attempts) publicDispatchLabels := by
  unfold ContainsPublicDispatch
  simp [publicDispatchLabels, publicHandler]

/-- The fixed dispatcher routes the decoded query and retains its charged memory state. -/
theorem publicHandler_dispatch [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    runPrefix (publicHandler attempts) (publicDispatchCost memory) ⟨96, memory⟩ =
      PMF.pure (some (false, ⟨publicDispatchLabel memory, publicDispatchMemory memory⟩,
        publicDispatchCost memory)) := by
  have result := publicDispatchHost (publicHandler attempts) publicDispatchLabels
    (publicHandler_containsDispatch attempts) memory
  exact result

/-- The dispatcher preserves the input operand, oracle index, query tag, RAM, and bits. -/
theorem publicDispatchMemory_data (memory : Memory) :
    (publicDispatchMemory memory).registers 8 = memory.registers 8 ∧
    (publicDispatchMemory memory).registers 9 = memory.registers 9 ∧
    (publicDispatchMemory memory).registers 10 = memory.registers 10 ∧
    (publicDispatchMemory memory).ram = memory.ram ∧ (publicDispatchMemory memory).bits = memory.bits := by
  by_cases hash : memory.registers 10 = 4#256 <;> simp [publicDispatchMemory, hash]

/-- The dispatcher returns to the selected block with all unused caller fuel. -/
theorem publicHandler_dispatchContinue [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (publicDispatchCost memory + fuel) ⟨96, memory⟩ =
      (run (publicHandler attempts) fuel ⟨publicDispatchLabel memory, publicDispatchMemory memory⟩).map
        (Option.map fun result => (result.1, result.2 + publicDispatchCost memory)) := by
  rw [run_after_prefix, publicHandler_dispatch, PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
