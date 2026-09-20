import Proof.Privacy.Source.Valid.SharedPipelineEventMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineEventRatioGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance pipelineEventRatioKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelineEventRatioKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype
set_option maxRecDepth 2048

/-- The complete two-phase pipeline event satisfies the shared real-source ratio. -/
theorem sharedPipelineTagEvent_sum_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, initial.hashOracle) after)
    (retainedNonfixed : SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, rest.encPRFOracle, rest.hashOracle) (before ++ after))
    (budget : (before ++ after).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    let reference := transcriptFinalState idealOracleHandler initial before
    (1 - ((54690772 + (364 * (reference.fixedTranscript ++ sharedFixedTranscriptRecords after).length : Nat)) /
      (2 : ENNReal) ^ 128)) *
      (∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (sharedPipelineTagEvent rest keys table input key initial before after tag)) ≤
      sharedRetainedRealPublicMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  dsimp only
  let reference := transcriptFinalState idealOracleHandler initial before
  have records := sharedIdealTranscriptFinal_fullPermutation initial before after empty compatible
  have lengthFits : (reference.fixedTranscript ++ sharedFixedTranscriptRecords after).length ≤ 2 ^ 101 := by
    rw [← records.length_eq]
    exact (sharedFixedTranscriptRecords_length (before ++ after)).trans budget
  have bound := sharedPipelineGoodTag_sum_le rest keys table input key reference
    (sharedFixedTranscriptRecords after) (before ++ after) records initial.fixedOracle retainedNonfixed lengthFits
  let factor := 1 - ((54690772 + (364 * (reference.fixedTranscript ++ sharedFixedTranscriptRecords after).length : Nat)) /
    (2 : ENNReal) ^ 128)
  have mass (tag : FullCircuitSource) :
      (if SharedPipelineTagGood rest keys table input key reference tag then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          sharedPipelineTagLowerMass rest keys input key tag reference (sharedFixedTranscriptRecords after) else 0) =
      factor * ((PMF.uniformOfFintype FullCircuitSource) tag *
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (sharedPipelineTagEvent rest keys table input key initial before after tag)) := by
    rw [sharedPipelineTagEvent_mass rest keys table input key initial before after tag empty compatible nonfixed]
    by_cases good : SharedPipelineTagGood rest keys table input key reference tag
    · rw [if_pos good, if_pos good]
      unfold sharedPipelineTagLowerMass
      dsimp only [factor]
      have reorder (a b c d e : ENNReal) : a * (b * (c * d * e)) = b * (c * (a * (d * e))) := by ac_rfl
      exact reorder _ _ _ _ _
    · rw [if_neg good, if_neg good, mul_zero, mul_zero]
  simp_rw [mass] at bound
  rw [ENNReal.tsum_mul_left] at bound
  exact bound

end
end Kriterion.ArgoMAC.Security
