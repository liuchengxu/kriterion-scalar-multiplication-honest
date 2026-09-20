import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The assembly map changes only the program counter. -/
def relocateConfiguration {source target : Nat} (labels : Fin source → Fin target)
    (state : Configuration source) : Configuration target := ⟨labels state.pc, state.memory⟩

/-- A full block retains every instruction, including its halt. -/
def ContainsMachine (host source : Machine)
    (labels : Fin (source.size + 1) → Fin (host.size + 1)) : Prop :=
  ∀ pc, host.code[(labels pc).val] = relocate labels (source.code[pc.val])

/-- Each assembled instruction preserves the complete memory outcome. -/
theorem relocate_step [BN254.FieldCertificate] (host source : Machine)
    (labels : Fin (source.size + 1) → Fin (host.size + 1))
    (present : ContainsMachine host source labels) (state : Configuration (source.size + 1)) :
    step host (relocateConfiguration labels state) =
      (step source state).map (Option.map fun result => (result.1, relocateConfiguration labels result.2)) := by
  unfold step
  simp only [relocateConfiguration, present state.pc]
  cases code : source.code[state.pc.val] <;>
    simp only [relocate, PMF.pure_map, Option.map_some, Option.map_none, relocateConfiguration]
  all_goals first
    | rfl
    | (split <;> simp [PMF.pure_map, relocateConfiguration])
    | (simp [PMF.map_bind, PMF.pure_map, relocateConfiguration])
  all_goals simp_all [apply_ite, PMF.pure_map, relocateConfiguration]

/-- Full assembly preserves every instruction charge and every failure outcome. -/
theorem relocate_run [BN254.FieldCertificate] (host source : Machine)
    (labels : Fin (source.size + 1) → Fin (host.size + 1))
    (present : ContainsMachine host source labels) (fuel : Nat)
    (state : Configuration (source.size + 1)) :
    run host fuel (relocateConfiguration labels state) =
      (run source fuel state).map
        (Option.map fun result => (relocateConfiguration labels result.1, result.2)) := by
  induction fuel generalizing state with
  | zero => simp [run, PMF.pure_map]
  | succ fuel ih =>
    rw [run, relocate_step host source labels present, PMF.bind_map, run, PMF.map_bind]
    congr 1
    funext outcome
    cases outcome with
    | none => simp [PMF.pure_map]
    | some outcome =>
      rcases outcome with ⟨halted, next⟩
      cases halted <;> simp [ih, PMF.pure_map, PMF.map_comp, Option.map_map, Function.comp_def]

end Kriterion.ArgoMAC.ArithmeticSimulator
