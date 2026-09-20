import Proof.Privacy.Distribution.SharedAdaptiveOutput
import Proof.Privacy.Source.AdaptiveGateSourceDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype circuitMaskSampleFintype
  instNonemptyPublicSample_2

/-- The adaptive mask transport keeps the shared oracle and both selected gate views. -/
theorem sharedAdaptiveGateMaskOutput_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      OutputRowRest → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype SharedOutputRowSource).bind (fun source =>
        (PMF.uniformOfFintype PublicSample).bind (fun sample =>
          (choose (publicMaskTable sample) source.val.2.2).bind fun selected =>
            observe (publicMaskTable sample) selected
              (retargetGateView sample selected.1 (idealSelectedOutput scalar selected.1 source.val)
                source.val.2.2) source.val.2.2))).toOuterMeasure event).toReal -
      (((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
        actualAdaptiveGateMaskRun scalar randomness.val choose observe)).toOuterMeasure event).toReal| ≤
      (2 : ℝ) ^ (-240 : ℤ) := by
  simp_rw [actualAdaptiveGateMaskRun_retarget]
  have bound := sharedAdaptiveOutput_observation_bound scalar witness parameter
    (fun rest => (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample) rest).map fun selected =>
        (selected.1, sample, selected.2)))
    (fun selected result rest => observe (publicMaskTable selected.2.1)
      (selected.1, selected.2.2) (retargetGateView selected.2.1 selected.1 result rest) rest) event
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using bound

end
end Kriterion.ArgoMAC.Security
