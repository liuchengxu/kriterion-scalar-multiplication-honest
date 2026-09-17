import Proof.Privacy.Transcript.EncPRFTranscript

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem weighted_fibers {Coin Tag : Type*} (coins : PMF Coin)
    (tag : Coin → Tag) (valid : Coin → Prop) (weight : Tag → ℝ≥0∞) :
    (∑' value, weight value * coins.toOuterMeasure {coin | tag coin = value ∧ valid coin}) =
      ∑' coin, coins coin * if valid coin then weight (tag coin) else 0 := by
  classical
  simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro coin
  by_cases member : valid coin
  · rw [tsum_eq_single (tag coin)]
    · simp [Set.indicator, member, mul_comm]
    · intro other different
      simp [Set.indicator, member, Ne.symm different]
  · simp [Set.indicator, member]

/-- This predicate excludes collisions in the actual shared whitening pads. -/
def EncSourceGood (source target : InputMacKey) : Prop :=
  ∀ index, Function.Injective (linkingPad source target index)

/-- The relative EncPRF count permits arbitrary source weights and unweighted tag sums. -/
theorem encFreshHash_weightedSource_mass_ge [Fintype Block]
    (source : InputMacKey) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block)
    (weight : InputMacKey → ℝ≥0∞) :
    (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords transcript) *
      (∑' target, (PMF.uniformOfFintype InputMacKey) target *
        if EncSourceGood source target then weight target else 0) ≤
    ∑' sample : (Block × Block) × PermutationOracle EncPRF.PermutationIndex Block,
      (PMF.uniformOfFintype ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block)) sample *
        if OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with encPRFOracle := sample.2} transcript then
            weight (EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source) else 0 := by
  classical
  let coins := PMF.uniformOfFintype
    ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block)
  let targetKey := fun sample : (Block × Block) × PermutationOracle EncPRF.PermutationIndex Block =>
    EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source
  let valid := fun sample : (Block × Block) × PermutationOracle EncPRF.PermutationIndex Block =>
    OracleTranscriptCompatible Garbling.oracleHandler {randomness with encPRFOracle := sample.2} transcript
  rw [← weighted_fibers coins targetKey valid weight]
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro target
  by_cases good : EncSourceGood source target
  · rw [if_pos good]
    have bound := encFreshHashTranscript_mass_ge source target randomness transcript compatible
      good budget lengthBound fits
    have weighted := mul_le_mul_right bound (weight target)
    convert weighted using 1
    · ac_rfl
  · simp only [if_neg good, mul_zero, zero_le]

end
end Kriterion.ArgoMAC.Security
