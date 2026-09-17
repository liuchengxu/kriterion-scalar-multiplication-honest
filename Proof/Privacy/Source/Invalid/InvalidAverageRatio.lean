import Proof.Privacy.Source.Invalid.InvalidEventAverage
import Proof.Privacy.Source.Invalid.RetainedInvalidCoefficient

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype transcriptOracleFintype
attribute [local instance] instNonemptyInputMacKey_proof_8

/-- The source guard permits one relative bound inside the normalized average. -/
theorem guardedRelativeAverage_le {First Second : Type*} (first : PMF First) (second : PMF Second)
    (condition : First → Second → Prop) (kept outer : Prop) [Decidable kept] [Decidable outer]
    (value factor actual result : ℝ≥0∞)
    (average : actual = ∑' a, first a * ∑' b, second b * if condition a b then (if kept then value else 0) else 0)
    (retained : kept → outer)
    (bound : kept → factor * (∑' a, first a * ∑' b, second b * if condition a b then value else 0) ≤ result) :
    factor * actual ≤ if outer then result else 0 := by
  by_cases keep : kept
  · rw [average, if_pos (retained keep)]
    simp only [if_pos keep]
    exact bound keep
  · rw [average]
    simp only [if_neg keep, ite_self, mul_zero, tsum_zero, zero_le]

/-- A compatible empty prefix records exactly the external fixed transcript. -/
theorem invalidReference_historyMembers (initial : SimulatorState)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before) :
    ∀ record, record ∈ (transcriptFinalState idealOracleHandler initial before).fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords before := by
  intro record
  rw [idealTranscriptFinal_fixedHistory initial before compatible, empty, List.append_nil, List.mem_reverse]

/-- The resampled linked event does not read the reference Enc or hash functions. -/
theorem actualLinkedTagKeyEvent_nonfixed_reference
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (selected : EncPRF.PermutationIndex → Bool) (labels : EncPRF.PermutationIndex → Block)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask
        (nonfixedSourceReference randomness enc hash) source lifts selected labels history =
      actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        source lifts selected labels history := rfl

/-- The actual linked tag mass does not depend on the resampled reference functions. -/
theorem retainedLinkedTagMass_nonfixed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys) (tag : FullCircuitSource)
    (input : AffineInput) (mac : InputMac) (history : List (Sigma Garbling.oracleSpec.Answer))
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    retainedLinkedTagMass {rest with encPRFOracle := enc, hashOracle := hash} outputKeys tag input mac history =
      retainedLinkedTagMass rest outputKeys tag input mac history := by
  unfold retainedLinkedTagMass
  apply congrArg (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
    ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
  rw [retainedFullSource_nonfixed, sourceReference_updateNonfixed]
  exact actualLinkedTagKeyEvent_nonfixed_reference _ _ _ _ _ _ _ _ _ _ _ _ enc hash

/-- Resampling the nonfixed functions removes any earlier reference-function update. -/
theorem invalidTagGoodEvent_nonfixed_rebase [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    (baseEnc enc : PermutationOracle EncPRF.PermutationIndex Block)
    (baseHash hash : EncPRF.HashOracle) :
    invalidTagGoodEvent {{rest with encPRFOracle := baseEnc, hashOracle := baseHash} with encPRFOracle := enc, hashOracle := hash}
        outputKeys table input key {{initial with encOracle := baseEnc, hashOracle := baseHash} with encOracle := enc, hashOracle := hash}
        before after tag =
      invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash} outputKeys table input key
        {initial with encOracle := enc, hashOracle := hash} before after tag := rfl

end
end Kriterion.ArgoMAC.Security
