import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A prefix stops at its instruction boundary and retains the machine's halt flag. -/
noncomputable def runPrefix [BN254.FieldCertificate] (machine : Machine) :
    Nat → Configuration (machine.size + 1) →
      PMF (Option (Bool × Configuration (machine.size + 1) × Nat))
  | 0, state => PMF.pure (some (false, state, 0))
  | count + 1, state => (step machine state).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next) => PMF.pure (some (true, next, 1))
      | some (false, next) => (runPrefix machine count next).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 1))

/-- Adjacent instruction prefixes add their actual costs. -/
theorem prefix_add [BN254.FieldCertificate] (machine : Machine) (first second : Nat)
    (state : Configuration (machine.size + 1)) :
    runPrefix machine (first + second) state = (runPrefix machine first state).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next, cost) => PMF.pure (some (true, next, cost))
      | some (false, next, cost) => (runPrefix machine second next).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + cost)) := by
  induction first generalizing state with
  | zero =>
      simp only [Nat.zero_add, runPrefix, PMF.pure_bind]
      simp only [Nat.add_zero]
      rw [show (Option.map fun result : Bool × Configuration (machine.size + 1) × Nat =>
        (result.1, result.2.1, result.2.2)) = id from by
          funext result; cases result <;> rfl, PMF.map_id]
  | succ first ih =>
      simp only [Nat.succ_add, runPrefix, ih, PMF.bind_bind]
      congr 1
      funext outcome
      cases outcome with
      | none => simp [PMF.pure_bind]
      | some outcome =>
          rcases outcome with ⟨halted, next⟩
          cases halted
          · simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
            congr 1
            funext result
            cases result with
            | none => simp [PMF.pure_map]
            | some result =>
                rcases result with ⟨halted, final, cost⟩
                cases halted <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def,
                  Option.map_map, Nat.add_assoc]
          · simp [PMF.pure_bind]

/-- A completed prefix passes its state and cost to the remaining machine execution. -/
theorem run_after_prefix [BN254.FieldCertificate] (machine : Machine) (first fuel : Nat)
    (state : Configuration (machine.size + 1)) :
    run machine (first + fuel) state = (runPrefix machine first state).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next, cost) => PMF.pure (some (next, cost))
      | some (false, next, cost) => (run machine fuel next).map
          (Option.map fun result => (result.1, result.2 + cost)) := by
  induction first generalizing state with
  | zero =>
      simp only [Nat.zero_add, runPrefix, PMF.pure_bind]
      simp only [Nat.add_zero]
      rw [show (Option.map fun result : Configuration (machine.size + 1) × Nat =>
        (result.1, result.2)) = id from by
          funext result; cases result <;> rfl, PMF.map_id]
  | succ first ih =>
      simp only [Nat.succ_add, run, runPrefix, ih, PMF.bind_bind]
      congr 1
      funext outcome
      cases outcome with
      | none => simp [PMF.pure_bind]
      | some outcome =>
          rcases outcome with ⟨halted, next⟩
          cases halted
          · simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
            congr 1
            funext result
            cases result with
            | none => simp [PMF.pure_map]
            | some result =>
                rcases result with ⟨halted, final, cost⟩
                cases halted <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def,
                  Option.map_map, Nat.add_assoc]
          · simp [PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
