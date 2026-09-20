import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointSource
import Proof.Privacy.Simulator.Arithmetic.SharedOnlineCutoffSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] onlineSamplingMemory onlineSamplingCoin onlinePreparedMemory encLinkSamples
attribute [local irreducible] onlineValidGateJoint onlineCurveMemory

/-- The full valid joint has the exact finite private-sampling and internal shared source law. -/
theorem onlineValidMemoryJoint_source [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (frame : Shared.Simulator.State) (input : AffineInput) (output : Point) (key : BaseField)
    (memory : Memory) (state : SharedOracleSource)
    (linkLaw : ∀ sampled, sampled ∈
        (onlineSamplingMemory attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support →
      let coin := onlineSamplingCoin attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
      let prepared := onlinePreparedMemory sampled.1 output coin
      (encLinkSamples attempts prepared state.family key []).map
        (fun linked => if linked.1.2.2 = 7466 then
          some (encLinkOutputMac linked.1.1 onlineLinkedBase, ({state with family := linked.2} : SharedOracleSource)) else none) =
        runSampledCutoff (sharedSourceCutoff attempts)
          (sharedCombinedProgram (link (frame.selectedCurve input) input (frame.labels input).inputMac)).toOracle state)
    (gateLaw : ∀ sampled, sampled ∈
        (onlineSamplingMemory attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support →
      let coin := onlineSamplingCoin attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
      let prepared := onlinePreparedMemory sampled.1 output coin
      ∀ linked, linked ∈ (encLinkSamples attempts prepared state.family key []).support → linked.1.2.2 = 7466 →
        (onlineValidGateJoint attempts frame input (frame.selectedPoints input output (Vector.ofFn coin.1) coin.2)
          (encLinkOutputMac linked.1.1 onlineLinkedBase) linked.1.1 {state with family := linked.2}).map
          (Option.map fun result => (result.1, result.2.2)) =
          (sharedCommandListCutoff attempts
            ((scheduleCommands (pipelineGateSchedule (frame.selectedCurve input)
              (frame.selectedPoints input output (Vector.ofFn coin.1) coin.2) input (frame.labels input).inputMac
              (encLinkOutputMac linked.1.1 onlineLinkedBase))).map sharedCommand) {state with family := linked.2}).map
                (Option.map fun result => (frame.labels input, result.2))) :
    (onlineValidMemoryJoint attempts frame input output key memory state).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts) (sharedOnlineTotalProgram attempts frame input (some output)) state := by
  rw [sharedOnlineTotalProgram_some, ← onlineSamplingCoin_source attempts
    (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))]
  simp only [onlineValidMemoryJoint, PMF.map_bind, PMF.bind_map, Function.comp_def]
  apply ThreePhase.bind_eq_on_support
  intro sampled member
  rw [← linkLaw sampled member]
  simp only [bindCutoff, PMF.bind_map]
  apply ThreePhase.bind_eq_on_support
  intro linked supported
  by_cases accepted : linked.1.2.2 = 7466
  · simp only [if_pos accepted, PMF.map_comp, Option.map_map, Function.comp_def]
    exact gateLaw sampled member linked supported accepted
  · simp only [Function.comp_def, if_neg accepted, PMF.pure_map, Option.map_none]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
