import Proof.Privacy.Source.ActualKeyMass
import Proof.Privacy.Collision.PadRestrictedCount
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The exact source fiber keeps the linking pad guard after the label split. -/
theorem actualIndependentSource_guardedKeyMass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : BaseField)
    (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (keys : RawCircuitGate → BitAdaptor.Key)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × (InputMacKey × InputMacKey))).toOuterMeasure
      {sample | (independentKeyLabelsEquiv selected sample.2).1 = publicLabels ∧
        independentFullCircuitSource outputKeys pointRandomness bridgeKey mask r1 r2
          sample.2.2 sample.2.1 (circuitSourceQuotients source) sample.1 = (lifts, sourceCiphertexts source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript ∧
        EncSourceGood sample.2.1 sample.2.2} =
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) ×
        (IndependentLabelWire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys
            (circuitSourceSlope source) lifts (circuitSourceTable source))
            (partialRawLabels (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
              (fun bucket _ => publicLabels (circuitBucketWire bucket))
              independentBucketWire (fun _ _ => 0) sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript ∧
          EncSourceGood ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).1
            ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).2} := by
  classical
  let event : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) × (IndependentLabelWire → Block)) :=
    {sample | RawGarblingMatches
      (rawGatesWithLabels (circuitRawGatePrescription keys
        (circuitSourceSlope source) lifts (circuitSourceTable source))
        (partialRawLabels (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
          (fun bucket _ => publicLabels (circuitBucketWire bucket))
          independentBucketWire (fun _ _ => 0) sample.2)) sample.1 ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with fixedKeyOracle := sample.1} transcript ∧
          EncSourceGood ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).1
            ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).2}
  have factor := uniform_key_event_mass (independentKeyLabelsEquiv selected) publicLabels event
  rw [← factor]
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq]
  apply and_congr_right
  intro labelsEqual
  have fiber := independentFullCircuitSource_fiber outputKeys pointRandomness bridgeKey mask r1 r2
    sample.2.2 sample.2.1 sample.1 source lifts randomizers residues
  rw [fiber]
  change _ ↔ RawGarblingMatches
      (rawGatesWithLabels _
        (partialRawLabels _ _ _ _ (independentKeyLabelsEquiv selected sample.2).2)) sample.1 ∧ _
  have labels := independentKeyLabels_source selected sample.2
  rw [labelsEqual] at labels
  rw [labels, rawGatesWithLabels_circuitSourceLabels]
  have inverse : (independentKeyLabelsEquiv selected).symm
      (publicLabels, (independentKeyLabelsEquiv selected sample.2).2) = sample.2 := by
    rw [← labelsEqual]
    exact (independentKeyLabelsEquiv selected).symm_apply_apply sample.2
  rw [inverse]
  rfl

end
end Kriterion.ArgoMAC.Security
