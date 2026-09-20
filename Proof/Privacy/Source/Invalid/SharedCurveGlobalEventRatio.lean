import Proof.Privacy.Bounds.SharedCurveLoss
import Proof.Privacy.Transcript.SharedTranscriptInvariant

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveGlobalEventGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance curveGlobalEventKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveGlobalEventKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype
set_option maxRecDepth 2048

/-- The guarded event averages the actual shared prefix, curve program, and suffix. -/
def sharedCurvePrefixEventMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  if OracleTranscriptCompatible idealOracleHandler initial before then
    ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (sharedCurveTagEvent rest keys table input key {initial with hashOracle := hash} before after tag)
  else 0

/-- One numerical coefficient applies to every retained curve source. -/
theorem sharedCurvePrefixEventMass_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = []) (enc : initial.encOracle = rest.encPRFOracle)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    ((1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after)))) *
        sharedCurvePrefixEventMass rest keys table input key initial before after ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  unfold sharedCurvePrefixEventMass
  split
  next compatible =>
    have records := sharedIdealTranscriptFinal_fullPermutation initial before after empty compatible
    have bounded : ((transcriptFinalState idealOracleHandler initial before).fixedTranscript ++
        sharedFixedTranscriptRecords after).length ≤ budget := by
      rw [← records.length_eq]
      exact (sharedFixedTranscriptRecords_length _).trans lengthBound
    exact (mul_le_mul_left (sharedCurveRelativeFactor_lower budget _ bounded (before ++ after)) _).trans
      (sharedCurveTagEvent_sum_ratio rest keys table input key initial before after empty compatible enc
        budget small lengthBound)
  next incompatible => simp only [mul_zero, zero_le]

/-- The full shared curve event stays below the actual real public event. -/
theorem sharedCurvePrefixEventMass_global_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : GarblingSourceRest → Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : ∀ rest, (initial rest).fixedTranscript = [])
    (enc : ∀ rest, (initial rest).encOracle = rest.encPRFOracle)
    (valid : ∀ rest, SimulatorInvariant (initial rest))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    ((1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after)))) *
        (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
          sharedCurvePrefixEventMass rest (outputKeys rest) table input key (initial rest) before after) ≤
      (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
        Pipeline.garble (outputKeys (sharedGarblingOracleKeyEquiv randomness).2) randomness.val.pointRandomness
          randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1 randomness.val.curveR2
          randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle randomness.val.inputMacKey = table ∧
        randomness.val.inputMacKey.encodeAffine input = key.encodeAffine input ∧
        OracleTranscriptCompatible sharedRealOracleHandler randomness (before ++ after)} := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  apply le_trans ?_ (sharedLinkedGlobalSourceMass_real_le witness parameter outputKeys unchanged
    table input (key.encodeAffine input) (before ++ after))
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rest
  letI := sharedIdealTranscriptFinal_nonempty (initial rest) before (valid rest)
  rw [mul_left_comm]
  exact mul_le_mul_right (sharedCurvePrefixEventMass_ratio rest (outputKeys rest) table input key
    (initial rest) before after (empty rest) (enc rest) budget small lengthBound) _

end
end Kriterion.ArgoMAC.Security
