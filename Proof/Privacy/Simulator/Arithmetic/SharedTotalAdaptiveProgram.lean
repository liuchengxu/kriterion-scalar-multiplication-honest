import Proof.Privacy.Simulator.Arithmetic.SharedSourceDecisionBound
import Proof.Privacy.Simulator.SimulatorTotalSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.Assumptions Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

/-- The finite private sampler supplies the same complete shared online program. -/
def sharedOnlineTotalProgram [FieldCertificate] [GroupCertificate] (attempts : Nat)
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Option Point) :
    OracleProgram SharedSimulatorMachine.combinedSpec Garbling.Labels 836423 :=
  match output with
  | none => (Program.weaken (sharedCombinedProgram (invalidProgram frame input)) (by decide : 3810 ≤ 836423)).toOracle
  | some point => .sample (SimulatorSampling.online.total attempts).law fun sample =>
      (sharedCombinedProgram (validProgram frame input point (Vector.ofFn sample.1) sample.2)).toOracle

/-- The complete finite private source retains both adaptive public phases. -/
def sharedAdaptiveTotalProgram [FieldCertificate] [GroupCertificate]
    {First Result : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : Shared.Simulator.State) (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Result secondBudget) :
    OracleProgram SharedSimulatorMachine.combinedSpec Result (firstBudget + (836423 + secondBudget)) :=
  ThreePhase.append (fun selected =>
    ThreePhase.append (fun labels => sharedExternalProgram (decide selected labels))
      (sharedOnlineTotalProgram attempts frame (input selected) (output selected))) (sharedExternalProgram choose)

/-- The online private fallback consumes at most 181 finite draw allowances. -/
theorem sharedOnlineTotalProgram_law [FieldCertificate] [GroupCertificate] (attempts : Nat)
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Option Point) (oracle : SharedState) :
    TotalLaw attempts 181 ((sharedOnlineProgram frame input output).run SharedSimulatorMachine.combinedEager oracle)
      ((sharedOnlineTotalProgram attempts frame input output).run SharedSimulatorMachine.combinedEager oracle) := by
  cases output with
  | none => exact (TotalLaw.exact attempts _).weaken (Nat.zero_le 181)
  | some point =>
    simp only [sharedOnlineProgram, sharedOnlineTotalProgram, OracleProgram.run_sample, Program.toOracle_run]
    exact (SimulatorSampling.Code.total_law attempts SimulatorSampling.online).map
      (fun sample => (sharedCombinedProgram (validProgram frame input point (Vector.ofFn sample.1) sample.2)).run SharedSimulatorMachine.combinedEager oracle)

/-- Both adaptive phases preserve the online private sampler's finite draw allowance. -/
theorem sharedAdaptiveTotalProgram_law [FieldCertificate] [GroupCertificate]
    {First Result : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : Shared.Simulator.State) (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Result secondBudget) (oracle : SharedState) :
    TotalLaw attempts 181 ((sharedAdaptiveProgram frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle)
      ((sharedAdaptiveTotalProgram attempts frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle) := by
  simp only [sharedAdaptiveProgram, sharedAdaptiveTotalProgram, ThreePhase.run_append, sharedExternalProgram_run]
  apply TotalLaw.sample
  intro selected
  exact (sharedOnlineTotalProgram_law attempts frame (input selected.1) (output selected.1) selected.2).bind
    (fun result => TotalLaw.exact attempts ((decide selected.1 result.1).run idealOracleHandler result.2))

/-- The complete finite online source includes all oracle cutoffs and private online draws. -/
theorem sharedAdaptiveTotalSource_decision_bound [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : Shared.Simulator.State) (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget) (state : SharedOracleSource) :
    advantage
      ((runSampledCutoff (sharedSourceCutoff attempts) (sharedAdaptiveTotalProgram attempts frame choose input output decide) state).map
        (fun result => (result.map Prod.fst).getD false))
      ((sharedSourceCompletion state).bind fun oracle =>
        ((sharedAdaptiveProgram frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle).map Prod.fst) ≤
      (firstBudget + (836604 + secondBudget)) * (2 : ℝ)⁻¹ ^ attempts := by
  have cutoff := sharedSource_decision_bound attempts (sharedAdaptiveTotalProgram attempts frame choose input output decide) state
  have sampling := (TotalLaw.sample (sharedSourceCompletion state) (fun oracle =>
    (sharedAdaptiveTotalProgram_law attempts frame choose input output decide oracle).map Prod.fst)).advantage
  unfold advantage at cutoff sampling ⊢
  have triangle := abs_sub_le
    ((((runSampledCutoff (sharedSourceCutoff attempts) (sharedAdaptiveTotalProgram attempts frame choose input output decide) state).map
      (fun result => (result.map Prod.fst).getD false)) true).toReal)
    ((((sharedSourceCompletion state).bind fun oracle =>
      ((sharedAdaptiveTotalProgram attempts frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle).map Prod.fst) true).toReal)
    ((((sharedSourceCompletion state).bind fun oracle =>
      ((sharedAdaptiveProgram frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle).map Prod.fst) true).toReal)
  rw [abs_sub_comm] at sampling
  simp only [Nat.cast_add, Nat.cast_ofNat] at cutoff ⊢
  linarith

end
end Kriterion.ArgoMAC.ArithmeticSimulator
