import Proof.Privacy.Source.EncSourceRatio
import Proof.Privacy.Source.HiddenHashSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem uniform_pair_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair : A × B, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

private theorem weighted_swap {A B : Type*} (first : PMF A) (second : PMF B)
    (weight : A → B → ℝ≥0∞) :
    (∑' a, first a * ∑' b, second b * weight a b) =
      ∑' b, second b * ∑' a, first a * weight a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ac_rfl

private theorem uniform_hashAnswer_weight [Fintype Block] [Fintype BaseField]
    (weight : EncPRF.HashOracle × (Block × Block) → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))) pair * weight pair) =
      ∑' hash, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        ∑' answer, (PMF.uniformOfFintype (Block × Block)) answer * weight (hash, answer) :=
  uniform_pair_weight weight

/-- The actual hidden hash link has a relative weighted source bound on every missed transcript. -/
theorem hiddenEncSource_weighted_mass_ge [Fintype Block] [Fintype BaseField]
    (hidden : BaseField) (source : InputMacKey) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : hidden ∉ transcriptHashInputs transcript)
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) (weight : InputMacKey → ℝ≥0∞) :
    (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      if OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := hash} transcript then
        (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
          encTranscriptFactor (encOracleTranscriptRecords transcript) *
          (∑' target, (PMF.uniformOfFintype InputMacKey) target *
            if EncSourceGood source target then weight target else 0) else 0) ≤
    ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
      (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          if OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := enc, hashOracle := hash} transcript then
              weight (EncPRF.transformKey enc ⟨(hash hidden).1, (hash hidden).2⟩ source) else 0 := by
  classical
  have resample (enc : PermutationOracle EncPRF.PermutationIndex Block) :=
    hiddenHashTranscript_weighted_eq hidden {randomness with encPRFOracle := enc} transcript miss
      (fun answer => weight (EncPRF.transformKey enc ⟨answer.1, answer.2⟩ source))
  dsimp only at resample
  simp_rw [resample, uniform_hashAnswer_weight]
  rw [weighted_swap]
  apply ENNReal.tsum_le_tsum
  intro hash
  apply mul_le_mul_right
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with hashOracle := hash} transcript
  · rw [if_pos compatible]
    have bound := encFreshHash_weightedSource_mass_ge source {randomness with hashOracle := hash}
      transcript compatible budget lengthBound fits weight
    rw [uniform_pair_weight] at bound
    rw [weighted_swap]
    exact bound
  · simp only [if_neg compatible, zero_le]

end
end Kriterion.ArgoMAC.Security
