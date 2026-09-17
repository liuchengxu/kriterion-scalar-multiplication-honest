import Proof.Privacy.Source.ActualLabelSource
import Proof.Privacy.Source.RealCircuitSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- A fixed public value leaves the exact uniform hidden source mass. -/
theorem uniform_public_hidden_mass {Public Hidden : Type}
    [Fintype Public] [Nonempty Public] [Fintype Hidden] [Nonempty Hidden]
    (value : Public) (event : Set Hidden) :
    (PMF.uniformOfFintype (Hidden × Public)).toOuterMeasure
      {sample | sample.2 = value ∧ sample.1 ∈ event} =
    (Fintype.card Public : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype Hidden).toOuterMeasure event := by
  classical
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  have mass : ∀ sample : Public,
      ((PMF.uniformOfFintype Hidden).map (fun hidden => (hidden, sample))).toOuterMeasure
        {pair | pair.2 = value ∧ pair.1 ∈ event} =
      if sample = value then (PMF.uniformOfFintype Hidden).toOuterMeasure event else 0 := by
    intro sample
    rw [PMF.toOuterMeasure_map_apply]
    by_cases same : sample = value
    · subst sample
      simp only [Set.preimage_setOf_eq, true_and, if_true]
      rfl
    · simp [Set.preimage_setOf_eq, same]
  simp only [Set.indicator_apply, mass]
  rw [tsum_eq_single value]
  · simp [PMF.uniformOfFintype_apply, Set.indicator_apply, tsum_fintype]
  · intro other different
    simp [different]

/-- This split keeps the oracle and hidden labels below the public label fiber. -/
def oracleKeySplit {Oracle Key Public Hidden : Type}
    (labels : Key ≃ Public × Hidden) :
    (Oracle × Key) ≃ ((Oracle × Hidden) × Public) where
  toFun sample := ((sample.1, (labels sample.2).2), (labels sample.2).1)
  invFun sample := (sample.1.1, labels.symm (sample.2, sample.1.2))
  left_inv sample := by simp
  right_inv sample := by simp

/-- An exact key split gives the full oracle event mass at fixed public labels. -/
theorem uniform_key_event_mass {Oracle Key Public Hidden : Type}
    [Fintype Oracle] [Nonempty Oracle] [Fintype Key] [Nonempty Key]
    [Fintype Public] [Nonempty Public] [Fintype Hidden] [Nonempty Hidden]
    (labels : Key ≃ Public × Hidden) (value : Public) (event : Set (Oracle × Hidden)) :
    (PMF.uniformOfFintype (Oracle × Key)).toOuterMeasure
      {sample | (labels sample.2).1 = value ∧ (sample.1, (labels sample.2).2) ∈ event} =
    (Fintype.card Public : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype (Oracle × Hidden)).toOuterMeasure event := by
  have mapped := uniform_public_hidden_mass value event
  rw [← map_uniformOfFintype_equivBetween (oracleKeySplit (Oracle := Oracle) labels),
    PMF.toOuterMeasure_map_apply] at mapped
  exact mapped


local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual linked source mass factors at the selected public labels. -/
theorem actualLinkedSource_keyMass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : SimulatorOracleCoin) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (keys : RawCircuitGate → BitAdaptor.Key)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | (selectedKeyLabelsEquiv selected sample.2).1 = publicLabels ∧
        actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
          sample.1 oracle.encOracle oracle.hashOracle sample.2 = (lifts, sourceCiphertexts source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} =
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) ×
        (EncPRF.PermutationIndex → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys
            (circuitSourceSlope source) lifts (circuitSourceTable source))
            (partialRawLabels (fun bucket branch => decide (branch = selected (circuitBucketWire bucket)))
              (fun bucket branch => publicLabels (circuitBucketWire bucket) ^^^
                circuitBucketPad oracle bridgeKey bucket branch)
              (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey) sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  classical
  let event : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) × (EncPRF.PermutationIndex → Block)) :=
    {sample | RawGarblingMatches
      (rawGatesWithLabels (circuitRawGatePrescription keys
        (circuitSourceSlope source) lifts (circuitSourceTable source))
        (partialRawLabels (fun bucket branch => decide (branch = selected (circuitBucketWire bucket)))
          (fun bucket branch => publicLabels (circuitBucketWire bucket) ^^^
            circuitBucketPad oracle bridgeKey bucket branch)
          (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey) sample.2)) sample.1 ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with fixedKeyOracle := sample.1} transcript}
  have factor := uniform_key_event_mass (selectedKeyLabelsEquiv selected) publicLabels event
  rw [← factor]
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq]
  apply and_congr_right
  intro labelsEqual
  have fiber := actualFullCircuitSource_fiber outputKeys pointRandomness bridgeKey r1 r2 mask sample.1
    oracle.encOracle oracle.hashOracle sample.2 source lifts randomizers residues
  dsimp only at fiber
  rw [fiber]
  change _ ↔ RawGarblingMatches
      (rawGatesWithLabels _
        (partialRawLabels _ _ _ _ (selectedKeyLabelsEquiv selected sample.2).2)) sample.1 ∧ _
  have labels := selectedKeyLabels_source oracle bridgeKey selected sample.2
  rw [labelsEqual] at labels
  rw [labels, rawGatesWithLabels_circuitSourceLabels]
  rfl

/-- The independent source mass factors at the selected curve labels. -/
theorem actualIndependentSource_keyMass [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
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
          {randomness with fixedKeyOracle := sample.1} transcript} =
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
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  classical
  let event : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) × (IndependentLabelWire → Block)) :=
    {sample | RawGarblingMatches
      (rawGatesWithLabels (circuitRawGatePrescription keys
        (circuitSourceSlope source) lifts (circuitSourceTable source))
        (partialRawLabels (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
          (fun bucket _ => publicLabels (circuitBucketWire bucket))
          independentBucketWire (fun _ _ => 0) sample.2)) sample.1 ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with fixedKeyOracle := sample.1} transcript}
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
  rfl


/-- This equivalence keeps every label in the actual input encoding. -/
def inputMacCoordinateEquiv : InputMac ≃ (EncPRF.PermutationIndex → Block) where
  toFun mac index := match index.1 with
    | .x => mac.x.get index.2
    | .y => mac.y.get index.2
  invFun labels := ⟨Vector.ofFn (fun index => labels (.x, index)),
    Vector.ofFn (fun index => labels (.y, index))⟩
  left_inv mac := by
    apply InputMac.ext <;> apply Vector.ext <;> intro index valid <;>
      simp only [Vector.getElem_ofFn, Vector.get_eq_getElem]
  right_inv labels := by
    funext index
    rcases index with ⟨coordinate, position⟩
    cases coordinate <;> simp only [Vector.get_ofFn]

/-- The selected coordinate source is the actual input MAC. -/
theorem selectedKeyLabels_inputMac (input : AffineInput) (key : InputMacKey) :
    (selectedKeyLabelsEquiv (inputSelectedLabelBit input) key).1 =
      inputMacCoordinateEquiv (key.encodeAffine input) := by
  funext index
  rcases index with ⟨coordinate, position⟩
  cases coordinate <;>
    simp [selectedKeyLabelsEquiv, inputSelectedLabelBit, inputMacCoordinateEquiv,
      InputMacKey.encodeAffine, InputMacKey.encode, encodeCoordinate, BitInput.ofAffine,
      inputKeyLabel, coordinateValues, Vector.get_eq_getElem]

/-- A fixed coordinate-label fiber is the actual public input-MAC fiber. -/
theorem selectedKeyLabels_public_iff (input : AffineInput) (key : InputMacKey) (mac : InputMac) :
    (selectedKeyLabelsEquiv (inputSelectedLabelBit input) key).1 = inputMacCoordinateEquiv mac ↔
      key.encodeAffine input = mac := by
  rw [selectedKeyLabels_inputMac, Equiv.apply_eq_iff_eq]


/-- This tape keeps every value except the fixed oracle and the input label key. -/
structure GarblingSourceRest where
  algebraic : GarblingAlgebraicData
  offsetsClamped : ∀ [FieldCertificate] [GroupCertificate], algebraic.point.offsets.IsClamped
  encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle

/-- This injection gives the remaining tape its existing finite source law. -/
def GarblingSourceRest.withKey (rest : GarblingSourceRest) (key : InputMacKey) :
    GarblingRandomnessRest := {
  algebraic := rest.algebraic
  offsetsClamped := rest.offsetsClamped
  inputMacKey := key
  encPRFOracle := rest.encPRFOracle
  hashOracle := rest.hashOracle }

instance : Fintype GarblingSourceRest := Fintype.ofInjective
  (fun rest => rest.withKey defaultSimulatorCoin.inputKey) (by
    intro first second same
    cases first
    cases second
    cases same
    rfl)

/-- The actual random tape separates the two coins used by the source count. -/
def garblingOracleKeyEquiv : Garbling.Randomness ≃
    ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) × GarblingSourceRest where
  toFun randomness := ((randomness.fixedKeyOracle, randomness.inputMacKey), {
    algebraic := (garblingRandomnessRest randomness).algebraic
    offsetsClamped := randomness.offsetsClamped
    encPRFOracle := randomness.encPRFOracle
    hashOracle := randomness.hashOracle })
  invFun sample := garblingRandomnessFixedOracleEquiv.symm
    (sample.1.1, sample.2.withKey sample.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- This identity samples the actual remaining tape before its oracle and label key. -/
theorem randomTape_oracleKey [Fintype Block] [Fintype Pipeline.FixedKeyIndex] (witness : Garbling.Randomness) (parameter : Nat) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    randomTape witness parameter =
      (PMF.uniformOfFintype GarblingSourceRest).bind fun rest =>
        (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).map
          (fun sample => garblingOracleKeyEquiv.symm (sample, rest)) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  change PMF.uniformOfFintype Garbling.Randomness = _
  rw [← map_uniformOfFintype_equivBetween garblingOracleKeyEquiv.symm,
    uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

end
end Kriterion.ArgoMAC.Security
