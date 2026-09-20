import Proof.Privacy.Source.Invalid.SharedCurveEventRatio
import Proof.Privacy.Bounds.AdaptiveLossAccounting

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The shared curve source pays its cross-branch and pad constants once. -/
theorem sharedCurveRelativeFactor_lower [Fintype Block]
    (budget historyLength : Nat) (bounded : historyLength ≤ budget)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) ≤
      sharedCurveRelativeFactor budget historyLength transcript := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  have numerator : 4 * budget + (54691280 + 364 * historyLength) ≤ 54691280 + 368 * budget := by omega
  have losses : ((4 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128 +
      ((54691280 + 364 * historyLength : Nat) : ENNReal) / (2 : ENNReal) ^ 128 ≤
      ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128 := by
    rw [← ENNReal.add_div, ← Nat.cast_add]
    exact mul_le_mul_left (by exact_mod_cast numerator) _
  have product := (tsub_le_tsub_left losses 1).trans
    (relativeLoss_product (((4 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128)
      (((54691280 + 364 * historyLength : Nat) : ENNReal) / (2 : ENNReal) ^ 128))
  have scaled := mul_le_mul_left product
    (encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript)))
  simpa only [sharedCurveRelativeFactor, card, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, mul_right_comm] using scaled

end
end Kriterion.ArgoMAC.Security
