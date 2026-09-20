import Proof.Privacy.Simulator.Arithmetic.SharedTotalAdaptiveProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.SimulatorMachine Security.SharedSimulatorMachine Security.BoundedIntegerSampling Security.OperationalOracle Security.SimulatorSampling
open scoped ENNReal
noncomputable section

/-- Successive common-mass bounds add their finite draw allowances. -/
theorem totalLaw_trans {A : Type} {attempts first second : Nat} {exact middle total : PMF A}
    (left : TotalLaw attempts first exact middle) (right : TotalLaw attempts second middle total) :
    TotalLaw attempts (first + second) exact total := by
  intro value
  calc
    retained attempts ^ (first + second) * exact value =
        retained attempts ^ second * (retained attempts ^ first * exact value) := by rw [pow_add]; ac_rfl
    _ ≤ retained attempts ^ second * middle value := by gcongr; exact left value
    _ ≤ total value := right value

/-- The optional finite interpreter retains the common exact program mass. -/
theorem sharedSourceCutoff_totalLaw (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram SharedSimulatorMachine.combinedSpec Result budget) (state : SharedOracleSource) :
    TotalLaw attempts budget ((runSampled sharedCombinedSourceHandler program state).map some)
      (runSampledCutoff (sharedSourceCutoff attempts) program state) := by
  intro result
  cases result with
  | none => simp [PMF.map_apply]
  | some value =>
    rw [mapSome_apply]
    exact runSampledCutoff_lower sharedCombinedSourceHandler (sharedSourceCutoff attempts)
      (retained attempts) tsub_le_self (sharedSourceCutoff_lower attempts) program state value

/-- The returned Boolean retains the common completed eager program mass. -/
theorem sharedSourceCutoff_decisionLaw (attempts : Nat) {budget : Nat}
    (program : OracleProgram SharedSimulatorMachine.combinedSpec Bool budget) (state : SharedOracleSource) :
    TotalLaw attempts budget
      ((sharedSourceCompletion state).bind fun oracle => (program.run SharedSimulatorMachine.combinedEager oracle).map Prod.fst)
      ((runSampledCutoff (sharedSourceCutoff attempts) program state).map
        (fun result => (result.map Prod.fst).getD false)) := by
  rw [sharedSource_resultLaw]
  have law := (sharedSourceCutoff_totalLaw attempts program state).map
    (fun result => (result.map Prod.fst).getD false)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some, Option.getD_some] using law

/-- The complete adaptive source retains exact mass after both online private and oracle cutoffs. -/
theorem sharedAdaptiveTotalSource_law [BN254.FieldCertificate] [BN254.GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : Shared.Simulator.State) (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → BN254.AffineInput) (output : First → Option BN254.Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget) (state : SharedOracleSource) :
    TotalLaw attempts (181 + (firstBudget + (836423 + secondBudget)))
      ((sharedSourceCompletion state).bind fun oracle =>
        ((sharedAdaptiveProgram frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle).map Prod.fst)
      ((runSampledCutoff (sharedSourceCutoff attempts) (sharedAdaptiveTotalProgram attempts frame choose input output decide) state).map
        (fun result => (result.map Prod.fst).getD false)) :=
  totalLaw_trans (TotalLaw.sample (sharedSourceCompletion state) (fun oracle =>
      (sharedAdaptiveTotalProgram_law attempts frame choose input output decide oracle).map Prod.fst))
    (sharedSourceCutoff_decisionLaw attempts (sharedAdaptiveTotalProgram attempts frame choose input output decide) state)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
