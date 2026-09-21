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

/-- A relocated simulator retains every oracle instruction and halt. -/
def ContainsSimulator (host source : Simulator)
    (labels : Fin (source.size + 1) → Fin (host.size + 1)) : Prop :=
  ∀ pc, host.code[(labels pc).val] = relocateSimulator labels (source.code[pc.val])

/-- Relocation preserves arithmetic, oracle transitions, and private memory. -/
theorem relocate_simulator_step [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (host source : Simulator) (labels : Fin (source.size + 1) → Fin (host.size + 1))
    (present : ContainsSimulator host source labels) (state : Configuration (source.size + 1))
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    host.step (relocateConfiguration labels state) oracle =
      (source.step state oracle).map (Option.map fun result =>
        (result.1, relocateConfiguration labels result.2.1, result.2.2)) := by
  have arithmetic : ContainsMachine host.arithmetic source.arithmetic labels := by
    intro pc
    simp only [Simulator.arithmetic, Vector.getElem_map, present pc]
    cases source.code[pc.val] <;> rfl
  unfold Simulator.step
  simp only [relocateConfiguration, present state.pc]
  cases code : source.code[state.pc.val] with
  | compute instruction =>
      simp only [relocateSimulator]
      rw [show step host.arithmetic ⟨labels state.pc, state.memory⟩ =
        (step source.arithmetic state).map (Option.map fun result =>
          (result.1, relocateConfiguration labels result.2)) from
        relocate_step host.arithmetic source.arithmetic labels arithmetic state]
      simp [PMF.map_comp, Option.map_map, Function.comp_def, relocateConfiguration]
  | query kind index input first second next =>
      simp only [relocateSimulator]
      split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def, relocateConfiguration]
  | lookup kind index input first second found next =>
      simp only [relocateSimulator]
      split <;> simp [PMF.pure_map, relocateConfiguration]
      split <;> rfl
  | program kind index input first second next =>
      simp only [relocateSimulator]
      split <;> simp [PMF.pure_map, Option.map_map, Function.comp_def, relocateConfiguration]

/-- Relocation preserves the complete run and its instruction charge. -/
theorem relocate_simulator_run [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (host source : Simulator) (labels : Fin (source.size + 1) → Fin (host.size + 1))
    (present : ContainsSimulator host source labels) (fuel : Nat)
    (state : Configuration (source.size + 1))
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    host.run fuel (relocateConfiguration labels state) oracle =
      (source.run fuel state oracle).map (Option.map fun result =>
        (relocateConfiguration labels result.1, result.2.1, result.2.2)) := by
  induction fuel generalizing state oracle with
  | zero => simp [Simulator.run, PMF.pure_map]
  | succ fuel ih =>
      rw [Simulator.run, relocate_simulator_step host source labels present,
        PMF.bind_map, Simulator.run, PMF.map_bind]
      congr 1
      funext outcome
      cases outcome with
      | none => simp [PMF.pure_map]
      | some outcome =>
          rcases outcome with ⟨halted, next, updated⟩
          cases halted <;> simp [ih, PMF.pure_map, PMF.map_comp, Option.map_map, Function.comp_def]

end Kriterion.ArgoMAC.ArithmeticSimulator
