import Proof.Privacy.Source.Invalid.SharedCurveNormalizedRatio
import Proof.Privacy.Source.Invalid.InvalidEventAverage

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveRestAverageKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveRestAverageKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
attribute [local irreducible] PMF.uniformOfFintype

/-- This retained mass keeps the actual nonfixed functions in both recording phases. -/
def sharedCurveRestEventMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key
        (sharedSourcePrefixReference reference rest) before after tag)

/-- A fresh pair of nonfixed functions gives the exact normalized retained event. -/
theorem sharedCurveRestEventMass_refreshed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) :
    (∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
      (PMF.uniformOfFintype _) nonfixed *
        sharedCurveRestEventMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
          keys table input key reference before after) =
      sharedCurveNonfixedEventMass rest keys table input key
        (sharedSourcePrefixReference reference rest) before after := by
  unfold sharedCurveRestEventMass sharedCurveNonfixedEventMass
  simp only [sharedCurveTagEvent_rest_refresh, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro tag
  simp only [mul_left_comm _ ((PMF.uniformOfFintype FullCircuitSource) tag),
    ENNReal.tsum_mul_left]
  congr 1
  exact uniform_pair_average_swap (fun enc hash =>
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key
        {sharedSourcePrefixReference reference rest with encOracle := enc, hashOracle := hash}
        before after tag))

/-- The actual source average equals the average with fresh nonfixed functions. -/
theorem sharedCurveRestEventMass_average [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Nonempty GarblingSourceRest]
    (keys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash, keys {rest with encPRFOracle := enc, hashOracle := hash} = keys rest)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) :
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      sharedCurveRestEventMass rest (keys rest) table input key reference before after) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      sharedCurveNonfixedEventMass rest (keys rest) table input key
        (sharedSourcePrefixReference reference rest) before after := by
  rw [← sourceRest_nonfixed_refresh
    (fun rest => sharedCurveRestEventMass rest (keys rest) table input key reference before after)]
  simp only [unchanged, sharedCurveRestEventMass_refreshed]

/-- The common transcript reference gives a uniform relative bound for every source. -/
theorem sharedCurveRestEventMass_normalized_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (encReference : PermutationTranscriptMatches reference.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      sharedCurveNonfixedEventMass rest keys table input key
        (sharedSourcePrefixReference reference rest) before after ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) (before ++ after) := by
  let refreshed := {rest with encPRFOracle := reference.encOracle, hashOracle := reference.hashOracle}
  let initial := sharedSourcePrefixReference reference refreshed
  have first : OracleTranscriptCompatible idealOracleHandler initial before := by
    rw [sharedIdealTranscriptCompatible_iff] at compatible ⊢
    exact compatible
  letI := sharedIdealTranscriptFinal_nonempty initial before
    (sharedSourcePrefixReference_invariant reference refreshed)
  have bound := sharedCurveNonfixedEventMass_reference_ratio rest keys table input key initial before after
    rfl first encReference budget small lengthBound
  exact bound

end
end Kriterion.ArgoMAC.Security
