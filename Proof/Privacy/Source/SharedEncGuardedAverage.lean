import Proof.Privacy.Source.SharedHiddenEncSource
import Proof.Privacy.Source.GuardedAverage

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance sharedGuardedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem weightedSwap {A B : Type*} (first : PMF A) (second : PMF B)
    (weight : A → B → ENNReal) :
    (∑' a, first a * ∑' b, second b * weight a b) =
      ∑' b, second b * ∑' a, first a * weight a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ac_rfl

private theorem uniformEvent {A : Type*} [Fintype A] [Nonempty A] (event : Set A) :
    (PMF.uniformOfFintype A).toOuterMeasure event =
      ∑' value, (PMF.uniformOfFintype A) value * if value ∈ event then 1 else 0 := by
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro value
  by_cases member : value ∈ event <;> simp [Set.indicator, member]

/-- The shared EncPRF count restores the linked source after the independent key average. -/
theorem sharedEnc_guarded_average_ge [Fintype Block] [Fintype BaseField]
    (rest : GarblingSourceRest) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (sharedLegacyTranscript transcript))
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card
      (EncQueryDomain (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) index) ≤ Fintype.card Block) :
    ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) ×
          ((EncPRF.PermutationIndex → Block) × InputMacKey))).toOuterMeasure
          {coin |
            let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
              (inputMacCoordinateEquiv mac, coin.2.1)
            RawGarblingMatches (sourceGatePrescription source coin.2.2 key lifts) (Shared.expandOracle coin.1) ∧
              OracleTranscriptCompatible (publicHandler id) (coin.1, rest.encPRFOracle, hash) transcript ∧
                EncSourceGood key coin.2.2}) ≤
    ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
      (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          sharedLinkedHiddenSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
            source lifts input mac transcript := by
  let key := fun labels => (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
    (inputMacCoordinateEquiv mac, labels)
  let factor := (1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
    encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))
  have law := guarded_average_factor (fun _ : EncPRF.PermutationIndex → Block => True)
    (fun fixed hash => OracleTranscriptCompatible (publicHandler id) (fixed, rest.encPRFOracle, hash) transcript)
    (fun labels target => EncSourceGood (key labels) target)
    (fun fixed labels target => RawGarblingMatches (sourceGatePrescription source target (key labels) lifts)
      (Shared.expandOracle fixed)) factor
  simp only [if_true, true_and] at law
  rw [← law]
  calc
    _ ≤ ∑' coin : (PermutationOracle Shared.FixedKeyIndex Block) × (EncPRF.PermutationIndex → Block),
        (PMF.uniformOfFintype _) coin *
          ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
            (PMF.uniformOfFintype _) enc * ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype _) hash *
              if OracleTranscriptCompatible (publicHandler id) (coin.1, enc, hash) transcript then
                (if RawGarblingMatches (sourceGatePrescription source
                  (EncPRF.transformKey enc ⟨(hash rest.algebraic.field.bridgeKey).1,
                    (hash rest.algebraic.field.bridgeKey).2⟩ (key coin.2)) (key coin.2) lifts)
                    (Shared.expandOracle coin.1) then 1 else 0) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro coin
      apply mul_le_mul_right
      exact sharedHiddenEncSource_weighted_mass_ge rest.algebraic.field.bridgeKey (key coin.2) rest coin.1
        transcript miss budget lengthBound fits
        (fun target => if RawGarblingMatches (sourceGatePrescription source target (key coin.2) lifts)
          (Shared.expandOracle coin.1) then 1 else 0)
    _ = _ := by
      rw [weightedSwap]
      apply tsum_congr
      intro enc
      apply congrArg (_ * ·)
      rw [weightedSwap]
      apply tsum_congr
      intro hash
      apply congrArg (_ * ·)
      rw [sharedLinkedHiddenSourceMass, uniformEvent]
      apply tsum_congr
      intro coin
      apply congrArg (_ * ·)
      change (if OracleTranscriptCompatible (publicHandler id) (coin.1, enc, hash) transcript then
        (if RawGarblingMatches (sourceGatePrescription source
          (EncPRF.transformKey enc (EncPRF.whiteningKeys hash rest.algebraic.field.bridgeKey) (key coin.2))
          (key coin.2) lifts) (Shared.expandOracle coin.1) then 1 else 0) else 0) = _
      by_cases compatible : OracleTranscriptCompatible (publicHandler id) (coin.1, enc, hash) transcript <;>
        by_cases matching : RawGarblingMatches (sourceGatePrescription source
          (EncPRF.transformKey enc (EncPRF.whiteningKeys hash rest.algebraic.field.bridgeKey) (key coin.2))
          (key coin.2) lifts) (Shared.expandOracle coin.1) <;>
        simp only [Set.mem_setOf_eq, key, compatible, matching, true_and, false_and, and_true, and_false, if_true, if_false]

end
end Kriterion.ArgoMAC.Security
