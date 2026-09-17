import Proof.Privacy.Source.FullSourceGood
import Proof.Privacy.Source.ActualLabelSource

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- Equal selected MACs give the same selected raw record. -/
theorem sourceGate_selectedRecord_rekey (source : CircuitMaskSample)
    (pointKey curveKey newPointKey newCurveKey : InputMacKey)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput)
    (curve : curveKey.encodeAffine input = newCurveKey.encodeAffine input)
    (point : pointKey.encodeAffine input = newPointKey.encodeAffine input)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (active : rawSlotBranch slot = circuitBucketInputBit input
      (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot))) :
    (sourceGatePrescription source pointKey curveKey lifts gate).slotRecord slot =
      (sourceGatePrescription source newPointKey newCurveKey lifts gate).slotRecord slot := by
  have label (first second : InputMacKey) :
      (sourceGatePrescription source second first lifts gate).label slot =
        circuitSourceLabels first second
          (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0)))
          (rawSlotBranch slot) := by
    rw [circuitSourceLabels_gate]
    cases slot <;> rfl
  have labels : (sourceGatePrescription source pointKey curveKey lifts gate).label slot =
      (sourceGatePrescription source newPointKey newCurveKey lifts gate).label slot := by
    rw [label, label]
    change rawSlotBranch slot = circuitBucketInputBit input
      (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0))) at active
    rw [active, circuitSourceLabels_selected, circuitSourceLabels_selected, curve, point]
  unfold RawGatePrescription.slotRecord
  rw [labels]
  rfl

/-- A fixed selected input MAC preserves the linked selected point MAC. -/
theorem linkedSelectedMac_rekey (coin : SimulatorCoin) (key : InputMacKey) (input : AffineInput)
    (same : key.encodeAffine input = coin.inputKey.encodeAffine input) :
    (EncPRF.transformKey coin.oracles.encOracle
      (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) key).encodeAffine input =
    (EncPRF.transformKey coin.oracles.encOracle
      (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey).encodeAffine input := by
  have mapped := congrArg (EncPRF.transformMac coin.oracles.encOracle
    (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) (BitInput.ofAffine input)) same
  simpa only [InputMacKey.encodeAffine, EncPRF.transformEncode] using mapped

/-- Equal selected MACs preserve both raw source conditions. -/
private theorem sourceGate_conditions_rekey (source : CircuitMaskSample)
    (pointKey curveKey newPointKey newCurveKey : InputMacKey)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (curve : curveKey.encodeAffine input = newCurveKey.encodeAffine input)
    (point : OnCurve input → pointKey.encodeAffine input = newPointKey.encodeAffine input) :
    let condition := fun gates : RawCircuitGate → RawGatePrescription =>
      (¬ ∀ index, Function.Injective (rawBucketOffset gates index)) ∨
      (¬ ∀ gate slot,
        rawSlotBranch slot = circuitBucketInputBit input
          (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) →
        (OnCurve input ∨ ∃ adaptor bit, gate = .inl (adaptor, bit)) →
        let record := (gates gate).slotRecord slot
        FreshPermutationPair (fixedOracleTranscriptRecords history)
          record.index record.domain record.range)
    condition (sourceGatePrescription source pointKey curveKey lifts) ↔
      condition (sourceGatePrescription source newPointKey newCurveKey lifts) := by
  dsimp only
  apply or_congr
  · rfl
  · apply not_congr
    apply forall_congr'
    intro gate
    apply forall_congr'
    intro slot
    apply imp_congr_right
    intro active
    apply imp_congr_right
    intro exposed
    rcases exposed with valid | ⟨adaptor, bit, rfl⟩
    · rw [sourceGate_selectedRecord_rekey source pointKey curveKey newPointKey newCurveKey
        lifts input curve (point valid) gate slot active]
    · have record :
          (sourceGatePrescription source pointKey curveKey lifts (.inl (adaptor, bit))).slotRecord slot =
          (sourceGatePrescription source newPointKey newCurveKey lifts (.inl (adaptor, bit))).slotRecord slot :=
        sourceGate_selectedRecord_rekey source pointKey curveKey pointKey newCurveKey
          lifts input curve rfl (.inl (adaptor, bit)) slot active
      rw [record]

/-- The actual bad flag depends only on the selected public input MAC. -/
theorem rawSourceBad_rekey (coin : SimulatorCoin) (key : InputMacKey)
    (source : CircuitMaskSample) (input : AffineInput)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (same : key.encodeAffine input = coin.inputKey.encodeAffine input) :
    rawSourceBad {coin with inputKey := key} source input history ↔
      rawSourceBad coin source input history := by
  exact sourceGate_conditions_rekey source _ key _ coin.inputKey _ input history same
    (fun _ => linkedSelectedMac_rekey coin key input same)

/-- An invalid source bad event uses only the selected curve MAC from its coin. -/
theorem rawSourceBad_offCurve_coin (coin other : SimulatorCoin)
    (source : CircuitMaskSample) (input : AffineInput)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (same : coin.inputKey.encodeAffine input = other.inputKey.encodeAffine input) :
    rawSourceBad coin source input history ↔ rawSourceBad other source input history := by
  exact sourceGate_conditions_rekey source _ coin.inputKey _ other.inputKey _ input history same
    (fun valid => (invalid valid).elim)

end

end Kriterion.ArgoMAC.Security
