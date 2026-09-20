import Construction.Simulator.PhaseDispatch
import Proof.Privacy.Simulator.Arithmetic.Blocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host consumes exactly two header bits and reaches the correct phase entry. -/
theorem phaseDispatch_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 7 → Fin (host.size + 1)) (present : ContainsPhaseDispatch host labels)
    (memory : Memory) (first second : Bool) (body : List Bool)
    (wire : memory.bits 0 = first :: second :: body) :
    runPrefix host 2 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels (phaseDispatchReturn first second), phaseDispatchMemory memory body⟩, 2)) := by
  have entry := present 0 (by decide)
  have left := present 1 (by decide)
  have right := present 2 (by decide)
  change host.code[(labels 0).val] = .pop 0 (labels 6) (labels 1) (labels 2) at entry
  change host.code[(labels 1).val] = .pop 0 (labels 6) (labels 3) (labels 4) at left
  change host.code[(labels 2).val] = .pop 0 (labels 6) (labels 5) (labels 6) at right
  cases first <;> cases second <;>
    simp [runPrefix, step, entry, left, right, wire, phaseDispatchReturn, phaseDispatchMemory,
      Function.update, PMF.pure_bind, PMF.pure_map]

/-- The host adds the exact two-instruction dispatch charge to its phase continuation. -/
theorem phaseDispatch_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 7 → Fin (host.size + 1)) (present : ContainsPhaseDispatch host labels)
    (memory : Memory) (first second : Bool) (body : List Bool)
    (wire : memory.bits 0 = first :: second :: body) (fuel : Nat) :
    run host (2 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels (phaseDispatchReturn first second), phaseDispatchMemory memory body⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  rw [run_after_prefix, phaseDispatch_prefix host labels present memory first second body wire, PMF.pure_bind]

/-- The dispatcher preserves RAM, registers, and both persistent private stacks. -/
theorem phaseDispatchMemory_frame (memory : Memory) (body : List Bool) :
    (phaseDispatchMemory memory body).ram = memory.ram ∧
    (phaseDispatchMemory memory body).registers = memory.registers ∧
    (phaseDispatchMemory memory body).bits 1 = memory.bits 1 ∧
    (phaseDispatchMemory memory body).bits 2 = memory.bits 2 ∧
    (phaseDispatchMemory memory body).bits 3 = memory.bits 3 := by
  simp [phaseDispatchMemory]

end Kriterion.ArgoMAC.ArithmeticSimulator
