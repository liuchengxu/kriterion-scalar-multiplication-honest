import Construction.Simulator.LinearProgram
import Proof.Privacy.Simulator.Arithmetic.Blocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains each linear instruction at its assigned label. -/
def ContainsLinear (host : Machine) (program : List LinearInstruction)
    (labels : Nat → Fin (host.size + 1)) : Prop :=
  ∀ index (valid : index < program.length),
    host.code[(labels index).val] = (program[index]).emit (labels (index + 1))

/-- Each emitted instruction has exactly the source memory effect. -/
theorem linear_step [BN254.FieldCertificate] (host : Machine)
    (instruction : LinearInstruction) (pc next : Fin (host.size + 1)) (memory : Memory)
    (selected : host.code[pc.val] = instruction.emit next) :
    step host ⟨pc, memory⟩ = PMF.pure (some (false, ⟨next, instruction.execute memory⟩)) := by
  cases instruction <;> simp [step, selected, LinearInstruction.emit, LinearInstruction.execute]

/-- The compiled block returns the exact source state and charges every instruction. -/
theorem linear_prefix [BN254.FieldCertificate] (host : Machine)
    (program : List LinearInstruction) (labels : Nat → Fin (host.size + 1))
    (present : ContainsLinear host program labels) (memory : Memory) :
    runPrefix host program.length ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels program.length, executeLinear program memory⟩,
        program.length)) := by
  induction program generalizing labels memory with
  | nil => simp [runPrefix, executeLinear]
  | cons instruction rest ih =>
      have first := present 0 (by simp)
      have tail : ContainsLinear host rest (fun index => labels (index + 1)) := by
        intro index valid
        exact present (index + 1) (by simpa using Nat.succ_lt_succ valid)
      simp only [List.length_cons, runPrefix]
      rw [linear_step host instruction (labels 0) (labels 1) memory (by simpa using first)]
      simp only [PMF.pure_bind]
      rw [ih (fun index => labels (index + 1)) tail]
      simp [executeLinear, PMF.pure_map]

/-- The compiled block passes its state and exact cost to the caller. -/
theorem linear_continue [BN254.FieldCertificate] (host : Machine)
    (program : List LinearInstruction) (labels : Nat → Fin (host.size + 1))
    (present : ContainsLinear host program labels) (memory : Memory) (fuel : Nat) :
    run host (program.length + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels program.length, executeLinear program memory⟩).map
        (Option.map fun result => (result.1, result.2 + program.length)) := by
  rw [run_after_prefix, linear_prefix host program labels present memory, PMF.pure_bind]

/-- The standalone compiler satisfies the same embedded-code condition. -/
theorem linearMachine_contains (program : List LinearInstruction)
    (fits : program.length < 2 ^ 256) :
    ContainsLinear (linearMachine program fits) program
      (fun index => ⟨min index program.length, by change min index program.length < program.length + 1; omega⟩) := by
  intro index valid
  simp [linearMachine, Nat.min_eq_left (Nat.le_of_lt valid),
    Nat.min_eq_left (show index + 1 ≤ program.length by omega), valid]

/-- A standalone linear program uses its length plus one executed instruction. -/
theorem linearMachine_run [BN254.FieldCertificate] (program : List LinearInstruction)
    (fits : program.length < 2 ^ 256) (memory : Memory) :
    run (linearMachine program fits) (program.length + 1)
      ⟨⟨0, by simp [linearMachine]⟩, memory⟩ =
      PMF.pure (some (⟨⟨program.length, by simp [linearMachine]⟩,
        executeLinear program memory⟩, program.length + 1)) := by
  have continuation := linear_continue (linearMachine program fits) program
    (fun index => ⟨min index program.length, by change min index program.length < program.length + 1; omega⟩)
    (linearMachine_contains program fits) memory 1
  have same := continuation
  simp only [Nat.min_self, Nat.zero_min] at same
  rw [same]
  simp [run, step, linearMachine, PMF.pure_map, Nat.add_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
