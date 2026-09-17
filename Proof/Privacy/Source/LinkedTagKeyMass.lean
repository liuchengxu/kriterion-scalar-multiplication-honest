import Proof.Privacy.Source.LinkedTagSourceRatio
import Proof.Privacy.Source.ActualLabelSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem uniform_pair_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

private theorem uniform_event_weight {A : Type*} [Fintype A] [Nonempty A] (event : Set A) :
    (PMF.uniformOfFintype A).toOuterMeasure event =
      ∑' value, (PMF.uniformOfFintype A) value * if value ∈ event then 1 else 0 := by
  classical
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro value
  by_cases member : value ∈ event <;> simp [Set.indicator, member]

/-- This event uses the actual linked garbler and every public transcript constraint. -/
def actualLinkedTagKeyEvent
    (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    Set (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) :=
  {coin | (selectedKeyLabelsEquiv selected coin.1.2).1 = publicLabels ∧
    actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
      coin.1.1 coin.2.1 coin.2.2 coin.1.2 = (lifts, sourceCiphertexts source) ∧
    OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with fixedKeyOracle := coin.1.1, encPRFOracle := coin.2.1, hashOracle := coin.2.2} transcript}

/-- Averaging the relative nonfixed count restores the actual selected-label source mass. -/
theorem actualLinkedTagKey_mass_ge [Fintype Block] [Fintype BaseField] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : bridgeKey ∉ transcriptHashInputs transcript)
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    (∑' coin : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey,
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) coin *
      if (selectedKeyLabelsEquiv selected coin.2).1 = publicLabels then
        (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          if OracleTranscriptCompatible Garbling.oracleHandler
              {randomness with fixedKeyOracle := coin.1, hashOracle := hash} transcript then
            (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
              encTranscriptFactor (encOracleTranscriptRecords transcript) *
              (∑' target, (PMF.uniformOfFintype InputMacKey) target *
                if EncSourceGood coin.2 target then
                  (if independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
                    target coin.2 (circuitSourceQuotients source) coin.1 =
                      (lifts, sourceCiphertexts source) then 1 else 0) else 0) else 0) else 0) ≤
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        source lifts selected publicLabels transcript) := by
  classical
  rw [uniform_event_weight]
  simp only [actualLinkedTagKeyEvent, Set.mem_setOf_eq]
  conv_rhs => rw [uniform_pair_weight]
  apply ENNReal.tsum_le_tsum
  intro coin
  apply mul_le_mul_right
  by_cases labels : (selectedKeyLabelsEquiv selected coin.2).1 = publicLabels
  · rw [if_pos labels]
    have bound := actualLinkedTagTranscript_mass_ge outputKeys pointRandomness bridgeKey r1 r2 mask coin.2
      {randomness with fixedKeyOracle := coin.1} source lifts transcript miss budget lengthBound fits
    apply bound.trans_eq
    conv_rhs => rw [uniform_pair_weight]
    apply tsum_congr
    intro enc
    apply congrArg (fun mass => (PMF.uniformOfFintype
      (PermutationOracle EncPRF.PermutationIndex Block)) enc * mass)
    apply tsum_congr
    intro hash
    simp only [labels, true_and]
    by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with fixedKeyOracle := coin.1, encPRFOracle := enc, hashOracle := hash} transcript
    · simp [compatible]
    · simp [compatible]
  · simp only [if_neg labels, zero_le]

end
end Kriterion.ArgoMAC.Security
