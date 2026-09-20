import Proof.Privacy.Source.SharedGateSourceEntrance
import Proof.Privacy.Distribution.SharedSourceRest

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype instNonemptyPublicSample_2

/-- The selected gate view depends only on the shared source rest. -/
def retargetSourceGateView (sample : PublicSample) (input : AffineInput)
    (result : Option Result) (rest : SourceOracleRest) : SelectedGateView :=
  (sample.curveRequest.retarget input
    (rest.1.1 + rest.1.2.value * (input.x ^ 3 + 3 - input.y ^ 2)),
    result.map fun value => retargetPointGateRequests sample.pointRequests input value.pointMacs)

/-- The source-rest view has the exact original gate effect. -/
theorem retargetGateView_source (sample : PublicSample) (input : AffineInput)
    (result : Option Result) (rest : OutputRowRest) :
    retargetGateView sample input result rest =
      retargetSourceGateView sample input result (outputSourceOracleRest rest) := rfl

/-- The shared ideal source uses the actual online coin after the adaptive input choice. -/
theorem actualSharedIdealGateSource_coin [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) :
    actualSharedIdealGateSourceRun scalar choose observe =
    (PMF.uniformOfFintype SharedMaskRetainedTape).bind (fun retained =>
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        (choose (publicMaskTable sample) retained.val.2.2).bind fun selected =>
          (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
            observe (publicMaskTable sample) selected
              (retargetSourceGateView sample selected.1 ((decodePoint selected.1).map fun point =>
                ⟨selected.1, outputTargets (scalarMultiplication scalar point) (Vector.ofFn coin.1) coin.2⟩)
                retained.val.2.2) retained.val.2.2) := by
  unfold actualSharedIdealGateSourceRun
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  apply congrArg ((PMF.uniformOfFintype PublicSample).bind)
  funext sample
  rw [sharedIdealOutput_encodingSource scalar
    (fun rest => choose (publicMaskTable sample) (outputSourceOracleRest rest))
    (fun selected result rest => observe (publicMaskTable sample) selected
      (retargetGateView sample selected.1 result rest) (outputSourceOracleRest rest))]
  simp_rw [retargetGateView_source]
  exact sharedOutputMaskRest_observation_eq
    (fun rest => (choose (publicMaskTable sample) rest).bind fun selected =>
      (PMF.uniformOfFintype ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
        observe (publicMaskTable sample) selected
          (retargetSourceGateView sample selected.1 ((decodePoint selected.1).map fun point =>
            ⟨selected.1, outputTargets (scalarMultiplication scalar point) (Vector.ofFn coin.1) coin.2⟩) rest) rest)

end
end Kriterion.ArgoMAC.Security
