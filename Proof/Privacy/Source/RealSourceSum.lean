import Proof.Privacy.Source.ActualKeyMass
import Proof.Privacy.Distribution.AdaptiveMaskDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- This reference fixes the retained oracles before the key source is sampled. -/
def GarblingSourceRest.reference (rest : GarblingSourceRest) : Garbling.Randomness :=
  garblingOracleKeyEquiv.symm
    ((defaultSimulatorCoin.oracles.fixedOracle, defaultSimulatorCoin.inputKey), rest)

/-- This coin keeps the exact retained hash and EncPRF functions. -/
def GarblingSourceRest.oracleCoin (rest : GarblingSourceRest) : SimulatorOracleCoin :=
  ⟨defaultSimulatorCoin.oracles.fixedOracle, rest.encPRFOracle, rest.hashOracle⟩

/-- This function extracts the actual source tag from one complete real tape. -/
def realTapeSource (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (randomness : Garbling.Randomness) : FullCircuitSource :=
  actualFullCircuitSource (outputKeys (garblingOracleKeyEquiv randomness).2)
    randomness.pointRandomness randomness.bridgeKey randomness.curveR1 randomness.curveR2
    randomness.curveMask randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
    randomness.inputMacKey

/-- The exact tape split preserves the actual source extraction. -/
theorem realTapeSource_inverse (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (rest : GarblingSourceRest) :
    realTapeSource outputKeys (garblingOracleKeyEquiv.symm (sample, rest)) =
      actualFullCircuitSource (outputKeys rest) rest.algebraic.point.pointRandomness
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
        rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2 := rfl

/-- The exact tape split preserves the sampled input key. -/
theorem garblingOracleKey_input
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (rest : GarblingSourceRest) :
    (garblingOracleKeyEquiv.symm (sample, rest)).inputMacKey = sample.2 := rfl

/-- This mass keeps the actual reconstructed keys below the selected public labels. -/
def linkedHiddenSourceMass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (rest : GarblingSourceRest) (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) ×
    (EncPRF.PermutationIndex → Block))).toOuterMeasure {sample |
      let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
        (inputMacCoordinateEquiv mac, sample.2)
      RawGarblingMatches (sourceGatePrescription source
        (EncPRF.transformKey rest.encPRFOracle
          (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key) key lifts) sample.1 ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {rest.reference with fixedKeyOracle := sample.1} transcript}

local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The real transcript depends only on the retained oracle functions. -/
theorem sourceRest_transcriptCompatible (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    OracleTranscriptCompatible Garbling.oracleHandler
      (garblingOracleKeyEquiv.symm (sample, rest)) transcript ↔
    OracleTranscriptCompatible Garbling.oracleHandler
      {rest.reference with fixedKeyOracle := sample.1} transcript := by
  rw [realOracleTranscriptCompatible_iff, realOracleTranscriptCompatible_iff]
  apply and_congr Iff.rfl
  induction transcript with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [NonFixedTranscriptCompatible, inductionHypothesis]
      all_goals rfl

/-- Each retained tape gives the actual source and input-MAC joint mass. -/
theorem retainedRealSource_mass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source rest.algebraic.point.pointRandomness
      rest.algebraic.field.curveR1 rest.algebraic.field.curveR2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
          rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
          rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2 =
            (lifts, sourceCiphertexts source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          (garblingOracleKeyEquiv.symm (sample, rest)) transcript} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        linkedHiddenSourceMass rest source lifts input mac transcript := by
  have mass := actualLinkedSource_keyMass outputKeys rest.algebraic.point.pointRandomness
    rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    rest.algebraic.field.curveMask rest.oracleCoin rest.reference source lifts
    (fun _ => (⟨0, 0⟩ : BitAdaptor.Key)) randomizers residues
    (inputSelectedLabelBit input) (inputMacCoordinateEquiv mac) transcript
  simp_rw [selectedKeyLabels_public_iff] at mass
  have gates (hidden : EncPRF.PermutationIndex → Block) :=
    linkedSource_gates rest.oracleCoin rest.algebraic.field.bridgeKey
      (inputSelectedLabelBit input) (inputMacCoordinateEquiv mac, hidden)
      (fun _ => (⟨0, 0⟩ : BitAdaptor.Key)) (circuitSourceSlope source) lifts (circuitSourceTable source)
  simp_rw [gates] at mass
  simpa only [linkedHiddenSourceMass, sourceGatePrescription, sourceRest_transcriptCompatible, GarblingSourceRest.oracleCoin] using mass


set_option maxRecDepth 4096 in
/-- The actual tape mass sums the hidden-label mass over every retained tape. -/
theorem realTapeSource_mass_sum [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (witness : Garbling.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (source : GarblingSourceRest → CircuitMaskSample)
    (lifts : GarblingSourceRest → RawCircuitGate → FullHashLift)
    (randomizers : ∀ rest, CircuitSourceRandomizers (source rest) rest.algebraic.point.pointRandomness
      rest.algebraic.field.curveR1 rest.algebraic.field.curveR2)
    (residues : ∀ rest gate, circuitSourceField (source rest) gate = ((lifts rest gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    (randomTape witness parameter).toOuterMeasure {randomness |
      randomness.inputMacKey.encodeAffine input = mac ∧
      realTapeSource outputKeys randomness =
        (lifts (garblingOracleKeyEquiv randomness).2,
          sourceCiphertexts (source (garblingOracleKeyEquiv randomness).2)) ∧
      OracleTranscriptCompatible Garbling.oracleHandler randomness transcript} =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        linkedHiddenSourceMass rest (source rest) (lifts rest) input mac transcript) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  rw [randomTape_oracleKey, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  congr 1
  have mass := retainedRealSource_mass rest (outputKeys rest) (source rest) (lifts rest)
    (randomizers rest) (residues rest) input mac transcript
  simp only [realTapeSource_inverse, garblingOracleKey_input, Equiv.apply_symm_apply]
  exact mass


/-- The retained curve source gives its exact masked curve result. -/
theorem circuitMaskSampleGarble_curveResult (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample) :
    (circuitMaskSampleGarble bridgeKey mask rows input source).curveRequest.result input =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  have result (sample : CurvePublicSample) :
      sample.request.result input = curveMaskResult input (curveSampleViewEquiv sample).1 := by
    simp [curveMaskResult, curveMaskRest, curveSampleViewEquiv, CurvePublicSample.request,
      CurveGateRequest.result]
    ring
  change (curveMaskSampleGarble bridgeKey mask input source.1).request.result input = _
  rw [result]
  simp only [curveMaskSampleGarble, Equiv.apply_symm_apply]
  exact (curveMaskViewEquiv bridgeKey mask input source.1.1).property

/-- A valid input uses the actual retained bridge key in the simulator schedule. -/
theorem circuitMaskSampleGarble_linkedSchedule (state : SimulatorState)
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey)
    (valid : OnCurve input) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    linkedPipelineGateSchedule state sample.curveRequest sample.pointRequests input (key.encodeAffine input) =
      pipelineGateSchedule sample.curveRequest sample.pointRequests input (key.encodeAffine input)
        ((EncPRF.transformKey state.encOracle (EncPRF.whiteningKeys state.hashOracle bridgeKey) key).encodeAffine input) := by
  dsimp only
  have result := circuitMaskSampleGarble_curveResult bridgeKey mask rows input source
  have residual : input.x ^ 3 + 3 - input.y ^ 2 = 0 := sub_eq_zero.mpr valid.symm
  rw [residual, mul_zero, add_zero] at result
  simp only [linkedPipelineGateSchedule, linkedPointInputMac, result, InputMacKey.encodeAffine,
    EncPRF.transformEncode]


/-- The full actual tag fixes every public table coefficient. -/
theorem actualFullCircuitSource_table (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (tag : actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask oracle
      encOracle hashOracle inputKey = (lifts, sourceCiphertexts source)) :
    Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2 oracle encOracle hashOracle inputKey =
      circuitMaskSourceTable bridgeKey mask.value
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) source := by
  have fiber := actualFullCircuitSource_fiber outputKeys pointRandomness bridgeKey r1 r2 mask
    oracle encOracle hashOracle inputKey source lifts randomizers residues
  dsimp only at fiber
  have matching := fiber.mp tag
  have pipeline := rawGarblingMatches_iff_pipeline outputKeys pointRandomness bridgeKey r1 r2 mask
    oracle encOracle hashOracle inputKey (⟨0, 0⟩ : AffineInput) source lifts randomizers residues
  dsimp only at pipeline
  exact (pipeline.mp matching).2


/-- The valid shared-label count uses the exact retained EncPRF shifts. -/
theorem linkedMixedLabels_source (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (input : AffineInput) (key : InputMacKey) (hidden : EncPRF.PermutationIndex → Block) :
    rawMixedLabels (circuitBucketInputBit input)
      (circuitBucketInputLabel (key.encodeAffine input)
        ((EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key).encodeAffine input))
      circuitBucketWire
      (fun bucket => circuitBucketPad oracle bridgeKey bucket (!(circuitBucketInputBit input bucket))) hidden =
    partialRawLabels (fun bucket branch => decide (branch = inputSelectedLabelBit input (circuitBucketWire bucket)))
      (fun bucket branch => inputMacCoordinateEquiv (key.encodeAffine input) (circuitBucketWire bucket) ^^^
        circuitBucketPad oracle bridgeKey bucket branch)
      (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey) hidden := by
  funext bucket branch
  have publicLabel := circuitSourceLabels_selected key
    (EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) input bucket
  rw [circuitSourceLabels_linked] at publicLabel
  have encoded := congrFun (selectedKeyLabels_inputMac input key) (circuitBucketWire bucket)
  change inputKeyLabel key (circuitBucketWire bucket) (inputSelectedLabelBit input (circuitBucketWire bucket)) = _ at encoded
  rw [circuitBucketInputBit_wire, encoded] at publicLabel
  unfold rawMixedLabels partialRawLabels
  rw [← publicLabel, circuitBucketInputBit_wire]
  cases selected : inputSelectedLabelBit input (circuitBucketWire bucket) <;>
    cases branch <;> simp [circuitBucketInputBit_wire, selected]

end
end Kriterion.ArgoMAC.Security
