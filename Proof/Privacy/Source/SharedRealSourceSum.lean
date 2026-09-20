import Proof.Privacy.Source.SharedRandomnessSource
import Proof.Privacy.Source.RealSourceSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
local instance sharedRealSourceKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance sharedRealSourceKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

abbrev sharedRealOracleSpec := publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex

/-- The shared real handler reads the actual three-slot evaluation oracle. -/
def sharedRealOracleHandler : OracleHandler sharedRealOracleSpec Shared.Randomness :=
  publicHandler Shared.evaluationOracle

/-- The reconstructed tape has exactly the sampled shared oracle and retained public functions. -/
theorem sharedOracleKey_view
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (rest : GarblingSourceRest) :
    Shared.evaluationOracle (sharedGarblingOracleKeyEquiv.symm (sample, rest)) =
      (sample.1, rest.encPRFOracle, rest.hashOracle) := by
  change (Shared.restrictOracle (Shared.expandOracle sample.1), rest.encPRFOracle, rest.hashOracle) = _
  rw [Shared.restrict_expand]

/-- A public transcript depends only on the tape's evaluation oracle. -/
theorem sharedTape_transcriptCompatible (randomness : Shared.Randomness)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible sharedRealOracleHandler randomness transcript ↔
      OracleTranscriptCompatible (publicHandler id) (Shared.evaluationOracle randomness) transcript := by
  induction transcript with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨request, answer⟩
      change (_ ∧ OracleTranscriptCompatible sharedRealOracleHandler randomness tail) ↔ _
      rw [ih]
      rfl

/-- The transcript keeps the same fixed, encryption, and hash answers after the source split. -/
theorem sharedSourceRest_transcriptCompatible (rest : GarblingSourceRest)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible sharedRealOracleHandler
      (sharedGarblingOracleKeyEquiv.symm (sample, rest)) transcript ↔
    OracleTranscriptCompatible (publicHandler id)
      (sample.1, rest.encPRFOracle, rest.hashOracle) transcript := by
  rw [sharedTape_transcriptCompatible, sharedOracleKey_view]

/-- The real source tag uses the actual shared oracle expansion. -/
def sharedRealTapeSource (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (randomness : Shared.Randomness) : FullCircuitSource :=
  actualFullCircuitSource (outputKeys (sharedGarblingOracleKeyEquiv randomness).2)
    randomness.val.pointRandomness randomness.val.bridgeKey randomness.val.curveR1 randomness.val.curveR2
    randomness.val.curveMask randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle
    randomness.val.inputMacKey

theorem sharedRealTapeSource_inverse (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (rest : GarblingSourceRest) :
    sharedRealTapeSource outputKeys (sharedGarblingOracleKeyEquiv.symm (sample, rest)) =
      actualFullCircuitSource (outputKeys rest) rest.algebraic.point.pointRandomness
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
        rest.algebraic.field.curveMask (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2 := by
  unfold sharedRealTapeSource
  rw [Equiv.apply_symm_apply]
  rfl

/-- The hidden source keeps the actual linked key and the complete shared transcript. -/
def sharedLinkedHiddenSourceMass [Fintype Block]
    (rest : GarblingSourceRest) (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) ×
    (EncPRF.PermutationIndex → Block))).toOuterMeasure {sample |
      let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
        (inputMacCoordinateEquiv mac, sample.2)
      RawGarblingMatches (sourceGatePrescription source
        (EncPRF.transformKey rest.encPRFOracle
          (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key) key lifts)
        (Shared.expandOracle sample.1) ∧
      OracleTranscriptCompatible (publicHandler id)
        (sample.1, rest.encPRFOracle, rest.hashOracle) transcript}

/-- The shared source factors at the exact selected public labels. -/
theorem sharedRetainedRealSource_mass [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source rest.algebraic.point.pointRandomness
      rest.algebraic.field.curveR1 rest.algebraic.field.curveR2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
          rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
          rest.algebraic.field.curveMask (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2 =
            (lifts, sourceCiphertexts source) ∧
        OracleTranscriptCompatible sharedRealOracleHandler
          (sharedGarblingOracleKeyEquiv.symm (sample, rest)) transcript} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        sharedLinkedHiddenSourceMass rest source lifts input mac transcript := by
  classical
  let event : Set ((PermutationOracle Shared.FixedKeyIndex Block) × (EncPRF.PermutationIndex → Block)) :=
    {sample |
      let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
        (inputMacCoordinateEquiv mac, sample.2)
      RawGarblingMatches (sourceGatePrescription source
        (EncPRF.transformKey rest.encPRFOracle
          (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key) key lifts)
        (Shared.expandOracle sample.1) ∧
      OracleTranscriptCompatible (publicHandler id)
        (sample.1, rest.encPRFOracle, rest.hashOracle) transcript}
  have factor := uniform_key_event_mass (selectedKeyLabelsEquiv (inputSelectedLabelBit input))
    (inputMacCoordinateEquiv mac) event
  change _ = (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) ×
      (EncPRF.PermutationIndex → Block))).toOuterMeasure event
  rw [← factor]
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq, selectedKeyLabels_public_iff]
  apply and_congr_right
  intro selected
  have labelEq := (selectedKeyLabels_public_iff input sample.2 mac).mpr selected
  have restored : (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
      (inputMacCoordinateEquiv mac, (selectedKeyLabelsEquiv (inputSelectedLabelBit input) sample.2).2) =
        sample.2 := by
    rw [← labelEq]
    exact Equiv.symm_apply_apply _ sample.2
  have fiber := actualFullCircuitSource_fiber outputKeys rest.algebraic.point.pointRandomness
    rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    rest.algebraic.field.curveMask (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle
    sample.2 source lifts randomizers residues
  dsimp only at fiber
  simp only [event, Set.mem_setOf_eq, restored, fiber, sharedSourceRest_transcriptCompatible]


set_option maxRecDepth 4096 in
/-- The shared tape mass sums the exact hidden-label mass over the remaining data. -/
theorem sharedRealTapeSource_mass_sum [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (source : GarblingSourceRest → CircuitMaskSample)
    (lifts : GarblingSourceRest → RawCircuitGate → FullHashLift)
    (randomizers : ∀ rest, CircuitSourceRandomizers (source rest) rest.algebraic.point.pointRandomness
      rest.algebraic.field.curveR1 rest.algebraic.field.curveR2)
    (residues : ∀ rest gate, circuitSourceField (source rest) gate = ((lifts rest gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
      randomness.val.inputMacKey.encodeAffine input = mac ∧
      sharedRealTapeSource outputKeys randomness =
        (lifts (sharedGarblingOracleKeyEquiv randomness).2,
          sourceCiphertexts (source (sharedGarblingOracleKeyEquiv randomness).2)) ∧
      OracleTranscriptCompatible sharedRealOracleHandler randomness transcript} =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        sharedLinkedHiddenSourceMass rest (source rest) (lifts rest) input mac transcript) := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedRandomTape_oracleKey, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  congr 1
  have mass := sharedRetainedRealSource_mass rest (outputKeys rest) (source rest) (lifts rest)
    (randomizers rest) (residues rest) input mac transcript
  simp only [sharedRealTapeSource_inverse, Equiv.apply_symm_apply]
  exact mass

end
end Kriterion.ArgoMAC.Security
