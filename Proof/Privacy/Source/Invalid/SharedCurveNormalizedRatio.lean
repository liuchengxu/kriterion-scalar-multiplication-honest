import Proof.Privacy.Source.Invalid.SharedCurveNonfixedAverage
import Proof.Privacy.Source.Invalid.SharedCurveGlobalEventRatio
import Proof.Privacy.Source.SharedSourcePrefixReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveNormalizedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveNormalizedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype

/-- This event mass averages both nonfixed functions before the source comparison. -/
def sharedCurveNonfixedEventMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
    ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
            (sharedCurveTagEvent rest keys table input key
              {initial with encOracle := enc, hashOracle := hash} before after tag)

/-- The exact nonfixed average removes the EncPRF factor from the relative bound. -/
theorem sharedCurveNonfixedEventMass_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = []) (enc : initial.encOracle = rest.encPRFOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (encReference : PermutationTranscriptMatches initial.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sharedCurveNonfixedEventMass rest keys table input key initial before after ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  have bound := sharedCurvePrefixEventMass_ratio rest keys table input key initial before after
    empty enc budget small lengthBound
  simp only [sharedCurvePrefixEventMass, if_pos compatible] at bound
  rw [mul_assoc, ← ENNReal.tsum_mul_left] at bound
  simp only [mul_left_comm (encTranscriptFactor _)] at bound
  simp_rw [sharedCurveTagEvent_encHash_average rest keys table input key initial before after _
    empty compatible encReference] at bound
  exact bound

/-- The refreshed linked source does not depend on its original nonfixed functions. -/
theorem sharedRefreshedLinkedSourceMass_rest_refresh [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    sharedRefreshedLinkedSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
      keys table input mac transcript = sharedRefreshedLinkedSourceMass rest keys table input mac transcript := by
  have source : ∀ tag, retainedFullSource {rest with encPRFOracle := enc, hashOracle := hash} tag =
      retainedFullSource rest tag := fun _ => rfl
  simp only [sharedRefreshedLinkedSourceMass, retainedFullTable, source]
  apply tsum_congr
  intro tag
  exact (ite_eq_ite _ _ _).mpr trivial

/-- A common compatible reference suffices for every retained source. -/
theorem sharedCurveNonfixedEventMass_reference_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (encReference : PermutationTranscriptMatches initial.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sharedCurveNonfixedEventMass rest keys table input key initial before after ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  have bound := sharedCurveNonfixedEventMass_ratio
    {rest with encPRFOracle := initial.encOracle, hashOracle := initial.hashOracle}
    keys table input key initial before after empty rfl compatible encReference budget small lengthBound
  simpa only [sharedCurveNonfixedEventMass, sharedCurveTagEvent_rest_refresh,
    sharedRefreshedLinkedSourceMass_rest_refresh] using bound

end
end Kriterion.ArgoMAC.Security
