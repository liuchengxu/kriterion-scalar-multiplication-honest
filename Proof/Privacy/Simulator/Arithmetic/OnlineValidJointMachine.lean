import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] onlineSamplingMemory onlineSamplingCoin onlinePreparedMemory encLinkSamples
attribute [local irreducible] onlineValidGateJoint onlineGateSamples onlineCurveMemory

private theorem finalCost (gate link preparation sampled prefixCost : Nat) :
    gate + link + preparation + sampled + prefixCost + 4 =
      gate + link + preparation + sampled + 1 + 3 + prefixCost := by omega

/-- The valid online joint preserves the actual sampler, link, gate, and preparation charges. -/
theorem onlineValidMemoryJoint_machine [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (frame : Shared.Simulator.State) (input : AffineInput) (output : Point) (key : BaseField)
    (memory : Memory) (state : SharedOracleSource)
    (gateLaw : ∀ sampled, sampled ∈
        (onlineSamplingMemory attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support →
      let coin := onlineSamplingCoin attempts (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
      let prepared := onlinePreparedMemory sampled.1 output coin
      ∀ linked, linked ∈ (encLinkSamples attempts prepared state.family key []).support → linked.1.2.2 = 7466 →
        (onlineValidGateJoint attempts frame input (frame.selectedPoints input output (Vector.ofFn coin.1) coin.2)
          (encLinkOutputMac linked.1.1 onlineLinkedBase) linked.1.1 {state with family := linked.2}).map
          (Option.map fun result => result.2.1) =
          (onlineGateSamples attempts linked.1.1).map
            (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none)) :
    (onlineValidMemoryJoint attempts frame input output key memory state).map
      (Option.map fun result => result.2.1) =
      (onlineValidSamples attempts memory input output state.family key []).map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none) := by
  simp only [onlineValidMemoryJoint, onlineValidSamples, onlineValidBranchSamples, onlineValidBodySamples,
    onlineSampledSamples, onlinePreparedSamples, onlineLinkSamples, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply ThreePhase.bind_eq_on_support
  intro sampled member
  apply ThreePhase.bind_eq_on_support
  intro linked supported
  by_cases accepted : linked.1.2.2 = 7466
  · simp only [if_pos accepted, onlineAfterLinkSamples, PMF.map_comp, Option.map_map, Function.comp_def]
    have law := gateLaw sampled member linked supported accepted
    have mapped := congrArg (PMF.map (Option.map fun result : Memory × Nat =>
      (result.1, result.2 + linked.1.2.1 +
        onlinePrepareCost (onlineSamplingCoin attempts
          (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled) +
        sampled.2 + onlinePrefixCost (some output) + 4))) law
    simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped
    rw [mapped]
    apply congrArg (fun f => PMF.map f (onlineGateSamples attempts linked.1.1))
    funext result
    split <;> simp only [Option.map_some, Option.map_none]
    · exact congrArg (fun cost => some (result.1.memory, cost))
        (finalCost result.2 linked.1.2.1
          (onlinePrepareCost (onlineSamplingCoin attempts
            (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled))
          sampled.2 (onlinePrefixCost (some output)))
  · simp only [if_neg accepted, onlineAfterLinkSamples, PMF.pure_map]
    rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
