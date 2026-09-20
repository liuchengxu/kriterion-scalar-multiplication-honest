import Proof.Privacy.Source.Valid.SharedPipelineEventRatio
import Proof.Privacy.Transcript.SharedTranscriptInvariant

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineGlobalEventGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance pipelineGlobalEventKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelineGlobalEventKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype
set_option maxRecDepth 2048

/-- This guarded mass keeps both phases of the actual shared pipeline event. -/
def sharedPipelinePrefixEventMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  if OracleTranscriptCompatible idealOracleHandler initial before ∧
      SharedNonFixedTranscriptCompatible (initial.fixedOracle, initial.encOracle, initial.hashOracle) after ∧
      SharedNonFixedTranscriptCompatible (initial.fixedOracle, rest.encPRFOracle, rest.hashOracle) (before ++ after) then
    ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
        (sharedPipelineTagEvent rest keys table input key initial before after tag)
  else 0

/-- One numerical coefficient applies to every retained pipeline source. -/
theorem sharedPipelinePrefixEventMass_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = []) (valid : SimulatorInvariant initial)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    (1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sharedPipelinePrefixEventMass rest keys table input key initial before after ≤
      sharedRetainedRealPublicMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  unfold sharedPipelinePrefixEventMass
  split
  next compatible =>
    letI := sharedIdealTranscriptFinal_nonempty initial before valid
    have records := sharedIdealTranscriptFinal_fullPermutation initial before after empty compatible.1
    have bounded : ((transcriptFinalState idealOracleHandler initial before).fixedTranscript ++
        sharedFixedTranscriptRecords after).length ≤ budget := by
      rw [← records.length_eq]
      exact (sharedFixedTranscriptRecords_length _).trans lengthBound
    have numerator : 54690772 + 364 * ((transcriptFinalState idealOracleHandler initial before).fixedTranscript ++
        sharedFixedTranscriptRecords after).length ≤ 54690772 + 364 * budget := by omega
    have losses : ((54690772 + 364 * ((transcriptFinalState idealOracleHandler initial before).fixedTranscript ++
        sharedFixedTranscriptRecords after).length : Nat) : ENNReal) / (2 : ENNReal) ^ 128 ≤
        ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128 :=
      mul_le_mul_left (by exact_mod_cast numerator) _
    apply (mul_le_mul_left (tsub_le_tsub_left losses 1) _).trans
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (sharedPipelineTagEvent_sum_ratio rest keys table input key initial before after empty compatible.1
        compatible.2.1 compatible.2.2 (lengthBound.trans small))
  next incompatible => simp only [mul_zero, zero_le]

/-- The full shared pipeline event stays below the actual real public event. -/
theorem sharedPipelinePrefixEventMass_global_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : GarblingSourceRest → Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : ∀ rest, (initial rest).fixedTranscript = [])
    (valid : ∀ rest, SimulatorInvariant (initial rest))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        sharedPipelinePrefixEventMass rest (outputKeys rest) table input key (initial rest) before after) ≤
      (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
        Pipeline.garble (outputKeys (sharedGarblingOracleKeyEquiv randomness).2) randomness.val.pointRandomness
          randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1 randomness.val.curveR2
          randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle randomness.val.inputMacKey = table ∧
        randomness.val.inputMacKey.encodeAffine input = key.encodeAffine input ∧
        OracleTranscriptCompatible sharedRealOracleHandler randomness (before ++ after)} := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedRealTapePublicMass_split, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rest
  rw [mul_left_comm]
  exact mul_le_mul_right (sharedPipelinePrefixEventMass_ratio rest (outputKeys rest) table input key
    (initial rest) before after (empty rest) (valid rest) budget small lengthBound) _

end
end Kriterion.ArgoMAC.Security
