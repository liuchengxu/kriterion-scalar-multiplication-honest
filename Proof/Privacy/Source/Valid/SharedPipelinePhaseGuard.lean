import Proof.Privacy.Source.Valid.SharedPipelinePhaseMass
import Proof.Privacy.Source.Valid.SharedPipelineEventNonfixed

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] circuitMaskSampleGarble retainedFullTable sharedGateSourceChoose sharedGateSourceObserve

/-- An incompatible nonfixed transcript has zero guarded pipeline mass. -/
theorem sharedPipelinePhaseWeight_zero_of_nonfixed [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (incompatible : ¬ SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle)
      (output.2.2.1 ++ output.2.2.2.2.2)) :
    sharedPipelinePhaseWeight adversary parameter auxiliary rest keys sample tag output = 0 := by
  unfold sharedPipelinePhaseWeight
  dsimp only
  apply le_antisymm ((sourceGoodMass_le _ _ _ _).trans_eq ?_) bot_le
  apply sharedGateSourcePhases_nonfixed_zero adversary parameter auxiliary (retainedFullTable rest keys tag)
    ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
    (fun input => selectedGateView
      (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
        (rowsForOutputKeys keys rest.algebraic.point.pointRandomness) input (retainedFullSource rest tag)) input)
    output
  intro compatible
  exact incompatible ((sharedNonFixedTranscriptCompatible_fixed _ reference _ _ _).mp compatible)

/-- The complete guarded phase formula retains the nonfixed compatibility condition. -/
theorem sharedPipelinePhaseWeight_guarded_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    sharedPipelinePhaseWeight adversary parameter auxiliary rest keys sample tag
      (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if SharedNonFixedTranscriptCompatible (referenceBefore.fixedOracle, rest.encPRFOracle, rest.hashOracle)
        (before ++ after) ∧ sample ∈ sharedPipelineTagEvent rest keys table selected.1 key
        (sharedSourcePrefixReference referenceBefore rest) before after tag then 1 else 0) := by
  by_cases nonfixed : SharedNonFixedTranscriptCompatible
      (referenceBefore.fixedOracle, rest.encPRFOracle, rest.hashOracle) (before ++ after)
  · simp only [nonfixed, true_and]
    exact sharedPipelinePhaseWeight_factor adversary parameter auxiliary rest keys sample tag table
      referenceBefore referenceAfter selected labels decision before after key valid bits mac firstCompatible
      secondCompatible (sharedSourcePrefixReference_compatible referenceBefore rest before firstCompatible
        ((sharedNonFixedTranscriptCompatible_append _ _ _).mp nonfixed).1)
  · rw [sharedPipelinePhaseWeight_zero_of_nonfixed adversary parameter auxiliary rest keys sample tag
      (table, selected, before, labels, decision, after) referenceBefore.fixedOracle nonfixed]
    simp only [nonfixed, false_and, if_false, mul_zero]

end
end Kriterion.ArgoMAC.Security
