import Proof.Privacy.Transcript.SharedPublicTranscript
import Proof.Privacy.Source.SharedRetainedProgramRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The real hidden source factors into the exact shared fixed transcript mass. -/
theorem sharedLinkedHiddenSourceMass_fixed [Fintype Block]
    (rest : GarblingSourceRest) (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript) :
    sharedLinkedHiddenSourceMass rest source lifts input mac transcript =
      ∑' labels, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) labels *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle |
            let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
              (inputMacCoordinateEquiv mac, labels)
            RawGarblingMatches (sourceGatePrescription source
              (EncPRF.transformKey rest.encPRFOracle
                (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key) key lifts)
              (Shared.expandOracle fixedOracle) ∧
            PermutationTranscriptMatches fixedOracle (sharedFixedTranscriptRecords transcript)} := by
  unfold sharedLinkedHiddenSourceMass
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro labels
  apply congrArg (_ * ·)
  rw [PMF.toOuterMeasure_map_apply]
  apply congrArg ((PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure)
  ext fixedOracle
  simp only [Set.mem_preimage, Set.mem_setOf_eq, sharedPublicTranscriptCompatible_iff]
  have other := (sharedNonFixedTranscriptCompatible_fixed fixedOracle reference
    rest.encPRFOracle rest.hashOracle transcript).mpr nonfixed
  simp only [other, and_true]

/-- The actual linked source equals the retained context's unused-label average. -/
theorem sharedLinkedHiddenSourceMass_context [Fintype Block]
    (rest : GarblingSourceRest) (context : SharedRetained.Context) (hidden : HiddenPublicSample)
    (mac : InputMac) (labels : context.activeCurveLabels = inputMacCoordinateEquiv mac)
    (linked : context.Linked rest.oracleCoin rest.algebraic.field.bridgeKey)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript) :
    sharedLinkedHiddenSourceMass rest (context.source hidden) (context.lifts hidden) context.input mac transcript =
      ∑' unused, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) unused *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle | RawGarblingMatches (context.gates (hidden, unused)) (Shared.expandOracle fixedOracle) ∧
            PermutationTranscriptMatches fixedOracle (sharedFixedTranscriptRecords transcript)} := by
  rw [sharedLinkedHiddenSourceMass_fixed rest _ _ _ _ transcript reference nonfixed]
  apply tsum_congr
  intro unused
  apply congrArg (_ * ·)
  rw [SharedRetained.linked_gates context rest.oracleCoin rest.algebraic.field.bridgeKey linked (hidden, unused)]
  have key : context.curveKey unused = (selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).symm
      (inputMacCoordinateEquiv mac, unused) := by
    unfold SharedRetained.Context.curveKey
    rw [labels]
  rw [key]
  rfl

end
end Kriterion.ArgoMAC.Security
