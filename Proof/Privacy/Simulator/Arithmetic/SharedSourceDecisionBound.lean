import Proof.Privacy.Simulator.Arithmetic.SharedAdaptiveProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.Assumptions Security Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- Forgetting the final source state preserves the exact completed eager result law. -/
theorem sharedSource_resultLaw {Result : Type} {budget : Nat}
    (program : OracleProgram combinedSpec Result budget) (state : SharedOracleSource) :
    (sharedSourceCompletion state).bind (fun eager => (program.run combinedEager eager).map Prod.fst) =
      (runSampled sharedCombinedSourceHandler program state).map Prod.fst := by
  have joint := congrArg (PMF.map Prod.fst) (sharedCombinedSource_adaptive_joint program state)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at joint
  have constant (result : Result × SharedOracleSource) :
      (sharedSourceCompletion result.2).map (fun _ => result.1) = PMF.pure result.1 := PMF.map_const _ _
  simp only [constant, PMF.bind_pure_comp] at joint
  exact joint

/-- A complete shared source program loses at most one cutoff allowance per operation. -/
theorem sharedSource_decision_bound (attempts : Nat) {budget : Nat}
    (program : OracleProgram combinedSpec Bool budget) (state : SharedOracleSource) :
    advantage
      ((runSampledCutoff (sharedSourceCutoff attempts) program state).map (fun result => (result.map Prod.fst).getD false))
      ((sharedSourceCompletion state).bind fun eager => (program.run combinedEager eager).map Prod.fst) ≤
        budget * (2 : ℝ)⁻¹ ^ attempts := by
  rw [sharedSource_resultLaw]
  have exactDecision : ((runSampled sharedCombinedSourceHandler program state).map some).map
      (fun result => (result.map Prod.fst).getD false) =
      (runSampled sharedCombinedSourceHandler program state).map Prod.fst := by
    rw [PMF.map_comp]
    rfl
  rw [← exactDecision]
  unfold advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact sharedSourceCutoff_event attempts program state _

/-- The complete adaptive source keeps the existing shared eager game within its explicit operation budget. -/
theorem sharedAdaptiveSource_decision_bound [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) {First : Type} {firstBudget secondBudget : Nat}
    (frame : Shared.Simulator.State)
    (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → BN254.AffineInput) (output : First → Option BN254.Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (state : SharedOracleSource) :
    advantage
      ((runSampledCutoff (sharedSourceCutoff attempts) (sharedAdaptiveProgram frame choose input output decide) state).map
        (fun result => (result.map Prod.fst).getD false))
      ((sharedSourceCompletion state).bind fun eager =>
        ((choose.run idealOracleHandler eager).bind fun selected =>
          (Shared.Simulator.simulator.simulateEncode {frame with oracle := selected.2}
            (input selected.1) (output selected.1)).bind fun encoded =>
              (decide selected.1 encoded.1).run idealOracleHandler encoded.2.oracle).map Prod.fst) ≤
      (firstBudget + (836423 + secondBudget)) * (2 : ℝ)⁻¹ ^ attempts := by
  simpa only [sharedAdaptiveProgram_run, Nat.cast_add, Nat.cast_ofNat] using
    sharedSource_decision_bound attempts (sharedAdaptiveProgram frame choose input output decide) state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
