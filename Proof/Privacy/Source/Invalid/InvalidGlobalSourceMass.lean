import Proof.Privacy.Source.Invalid.InvalidRestRefreshNormalized
import Proof.Privacy.Source.LinkedGlobalSourceMass
import Proof.Privacy.Source.RealEndpointPhaseMass
import Proof.Privacy.Source.Invalid.InvalidRebasedBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem refresh_relative_sum {Rest Nonfixed Tag : Type*}
    (rests : PMF Rest) (coins : PMF Nonfixed) (tags : PMF Tag) (factor : ℝ≥0∞)
    (mass : Rest → ℝ≥0∞) (refreshed : Rest → Nonfixed → ℝ≥0∞)
    (event upper : Rest → Tag → ℝ≥0∞) (guard : Rest → Prop)
    {guardDec : ∀ rest, Decidable (guard rest)}
    (refresh : (∑' rest, rests rest * mass rest) =
      ∑' rest, rests rest * ∑' coin, coins coin * refreshed rest coin)
    (expand : ∀ rest, (∑' coin, coins coin * refreshed rest coin) =
      ∑' tag, tags tag * @ite ℝ≥0∞ (guard rest) (guardDec rest) (event rest tag) 0)
    (count : ∀ rest tag, guard rest → factor * event rest tag ≤ upper rest tag) :
    factor * (∑' rest, rests rest * mass rest) ≤
      ∑' rest, rests rest * ∑' tag, tags tag * upper rest tag := by
  rw [refresh, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rest
  rw [expand rest, mul_left_comm factor (rests rest)]
  apply mul_le_mul_right
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro tag
  rw [mul_left_comm factor (tags tag)]
  apply mul_le_mul_right
  by_cases kept : guard rest
  · rw [if_pos kept]
    exact count rest tag kept
  · rw [if_neg kept, mul_zero]
    exact bot_le

attribute [local instance] publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
attribute [local instance] instNonemptyInputMacKey_proof_8

set_option maxRecDepth 4096 in
/-- The normalized invalid event sum satisfies the actual global linked-source bound. -/
def invalidRestEventMass_global_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Fintype FullCircuitSource] [Nonempty FullCircuitSource]
    (sourceWitness nonfixedWitness : Garbling.Randomness) (scalar : ScalarField)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible nonfixedWitness (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv sourceWitness).2⟩
  exact refresh_relative_sum (PMF.uniformOfFintype GarblingSourceRest)
    (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))
    (PMF.uniformOfFintype FullCircuitSource)
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block)
    (invalidRestEventMass scalar table input key reference before after)
    (fun rest nonfixed => invalidRestEventMass scalar table input key reference before after
      {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}) _
    (fun rest tag => if FullSourceComplete tag.1 ∧
      retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag = table then
      (fullSourceTagDensity tag)⁻¹ * retainedLinkedTagMass rest
        (outputKeys construction scalar rest.reference.offsets) tag input (key.encodeAffine input) (before ++ after) else 0)
    (fun rest => rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (invalidRestEventMass_refresh scalar table input key reference before after).symm
    (fun rest => invalidRestEventMass_refreshed_normalized scalar table input key reference before after rest)
    (fun rest tag miss => by
      rcases tag with ⟨lifts, tables⟩
      have bound := invalidRestRebased_mass_ge rest
        (outputKeys construction scalar rest.reference.offsets) table input key reference nonfixedWitness
        before after lifts tables invalid compatible nonfixed miss budget small bounded
      exact bound)


end
end Kriterion.ArgoMAC.Security
