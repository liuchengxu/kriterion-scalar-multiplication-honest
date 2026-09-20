import Proof.Privacy.Source.SharedRealSourceLower
import Proof.Privacy.Source.SourceRestRefresh

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1

private theorem pairAverage {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A → B → ENNReal) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair.1 pair.2) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight first second := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- This mass averages the actual linked source over the two nonfixed functions. -/
def sharedRefreshedLinkedSourceMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  ∑' tag : FullCircuitSource,
    if FullSourceComplete tag.1 ∧ retainedFullTable rest keys tag = table then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
        ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
          (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
            ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
              sharedLinkedHiddenSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
                (retainedFullSource rest tag) tag.1 input mac transcript
    else 0

/-- The refreshed complete-tag sum stays below the refreshed actual public event. -/
theorem sharedRefreshedLinkedSourceMass_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    sharedRefreshedLinkedSourceMass rest keys table input mac transcript ≤
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype _) nonfixed *
          sharedRetainedRealPublicMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
            keys table input mac transcript := by
  let weight := fun nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle =>
    ∑' tag : FullCircuitSource,
      if FullSourceComplete tag.1 ∧ retainedFullTable rest keys tag = table then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          sharedLinkedHiddenSourceMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
            (retainedFullSource rest tag) tag.1 input mac transcript else 0
  have average : sharedRefreshedLinkedSourceMass rest keys table input mac transcript =
      ∑' nonfixed, (PMF.uniformOfFintype _) nonfixed * weight nonfixed := by
    rw [sharedRefreshedLinkedSourceMass]
    simp only [weight, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro tag
    by_cases kept : FullSourceComplete tag.1 ∧ retainedFullTable rest keys tag = table
    · simp only [if_pos kept]
      rw [pairAverage (fun enc hash =>
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          sharedLinkedHiddenSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
            (retainedFullSource rest tag) tag.1 input mac transcript)]
      simp only [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro enc
      apply tsum_congr
      intro hash
      exact (mul_left_comm _ _ _).trans (congrArg (_ * ·) (mul_left_comm _ _ _))
    · simp only [if_neg kept, mul_zero, tsum_zero]
  rw [average]
  apply ENNReal.tsum_le_tsum
  intro nonfixed
  apply mul_le_mul_right
  exact sharedRetainedRealSource_fullTag_sum_le
    {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2} keys table input mac transcript

/-- Refreshing the two nonfixed functions preserves the shared actual public mass. -/
theorem sharedRealPublicMass_refresh [Fintype Block] [Nonempty GarblingSourceRest]
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype _) nonfixed *
          sharedRetainedRealPublicMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
            (outputKeys rest) table input mac transcript) =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        sharedRetainedRealPublicMass rest (outputKeys rest) table input mac transcript := by
  simpa only [unchanged] using sourceRest_nonfixed_refresh
    (fun rest => sharedRetainedRealPublicMass rest (outputKeys rest) table input mac transcript)

/-- The refreshed shared linked source stays below the actual public event on the full tape. -/
def sharedLinkedGlobalSourceMass_real_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :=
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  let bound := ENNReal.tsum_le_tsum (fun rest : GarblingSourceRest =>
    mul_le_mul_right (sharedRefreshedLinkedSourceMass_le rest (outputKeys rest) table input mac transcript)
      ((PMF.uniformOfFintype GarblingSourceRest) rest))
  bound.trans_eq ((sharedRealPublicMass_refresh outputKeys unchanged table input mac transcript).trans
    (sharedRealTapePublicMass_split witness parameter outputKeys table input mac transcript).symm)

end
end Kriterion.ArgoMAC.Security
