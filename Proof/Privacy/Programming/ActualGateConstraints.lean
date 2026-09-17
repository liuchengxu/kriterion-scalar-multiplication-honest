import Proof.Privacy.Source.ActualMaskSource
import Proof.Privacy.Transcript.RealTranscriptMass

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- This map selects the actual input label pair for each circuit gate. -/
def circuitGateKey (pointKey inputKey : InputMacKey) : RawCircuitGate → BitAdaptor.Key
  | .inl (adaptor, bit) => (![inputKey.x, inputKey.x, inputKey.x, inputKey.y, inputKey.y] adaptor).get bit
  | .inr (_, .inl (adaptor, bit)) => (![pointKey.y, pointKey.y, pointKey.y, pointKey.x] adaptor).get bit
  | .inr (_, .inr (.inl (adaptor, bit))) => (![pointKey.x, pointKey.x, pointKey.x] adaptor).get bit
  | .inr (_, .inr (.inr (adaptor, bit))) =>
      (![pointKey.y, pointKey.y, pointKey.y, pointKey.x, pointKey.x] adaptor).get bit

/-- This map retains the source hash field at each actual gate. -/
def circuitSourceField (source : CircuitMaskSample) : RawCircuitGate → BaseField
  | .inl (adaptor, bit) => source.1.1.2 adaptor bit
  | .inr (row, .inl (adaptor, bit)) => (source.2 row).1.1.2 adaptor bit
  | .inr (row, .inr (.inl (adaptor, bit))) => (source.2 row).2.1.1.2 adaptor bit
  | .inr (row, .inr (.inr (adaptor, bit))) => (source.2 row).2.2.1.2 adaptor bit

/-- This map retains the public ciphertext at each actual gate. -/
def circuitSourceTable (source : CircuitMaskSample) : RawCircuitGate → BitAdaptor.Table
  | .inl (adaptor, bit) => (source.1.2.1 adaptor).get bit
  | .inr (row, .inl (adaptor, bit)) => ((source.2 row).1.2.1 adaptor).get bit
  | .inr (row, .inr (.inl (adaptor, bit))) => ((source.2 row).2.1.2.1 adaptor).get bit
  | .inr (row, .inr (.inr (adaptor, bit))) => ((source.2 row).2.2.2.1 adaptor).get bit

/-- These slopes use the actual triangular mask equations. -/
def circuitSourceSlope (source : CircuitMaskSample) : RawCircuitGate → BaseField
  | .inl (adaptor, _) =>
      let data := source.1.1
      ![-data.1 0, -DigitAdaptor.fromBits (data.2 0), -DigitAdaptor.fromBits (data.2 1),
        -data.1 1, -DigitAdaptor.fromBits (data.2 3)] adaptor
  | .inr (row, .inl (adaptor, _)) =>
      let data := (source.2 row).1.1
      ![-data.1 2, -data.1 3, -(data.1 1 + DigitAdaptor.fromBits (data.2 1)),
        -(data.1 0 + DigitAdaptor.fromBits (data.2 0))] adaptor
  | .inr (row, .inr (.inl (adaptor, _))) =>
      let data := (source.2 row).2.1.1
      ![-data.1 2, -(data.1 1 + DigitAdaptor.fromBits (data.2 0)),
        -(data.1 0 + DigitAdaptor.fromBits (data.2 1))] adaptor
  | .inr (row, .inr (.inr (adaptor, _))) =>
      let data := (source.2 row).2.2.1
      ![-data.1 1, -data.1 3, -(data.1 0 + DigitAdaptor.fromBits (data.2 1)),
        -data.1 2, -(DigitAdaptor.fromBits (data.2 0) + DigitAdaptor.fromBits (data.2 3))] adaptor

/-- These quotients retain the complete hash fibers of the source. -/
def circuitSourceQuotients (source : CircuitMaskSample) : CircuitMaskQuotients :=
  (source.1.2.2, fun row => ((source.2 row).1.2.2, (source.2 row).2.1.2.2, (source.2 row).2.2.2.2))

/-- This condition fixes the actual independent field randomizers. -/
def CircuitSourceRandomizers (source : CircuitMaskSample)
    (pointRandomness : FieldMacToECMac.Randomness) (r1 r2 : BaseField) : Prop :=
  source.1.1.1 = ![r1, r2] ∧ ∀ row,
    (source.2 row).1.1.1 = ![(pointRandomness.get row).x.r1, (pointRandomness.get row).x.r2,
      (pointRandomness.get row).x.r3, (pointRandomness.get row).x.r5] ∧
    (source.2 row).2.1.1.1 = ![(pointRandomness.get row).y.r1,
      (pointRandomness.get row).y.r4, (pointRandomness.get row).y.r5] ∧
    (source.2 row).2.2.1.1 = ![(pointRandomness.get row).z.r2, (pointRandomness.get row).z.r3,
      (pointRandomness.get row).z.r4, (pointRandomness.get row).z.r5]

/-- This prescription fixes the actual labels, slopes, full hash lifts, and ciphertexts. -/
def sourceGatePrescription (source : CircuitMaskSample) (pointKey inputKey : InputMacKey)
    (lifts : RawCircuitGate → FullHashLift) : RawCircuitGate → RawGatePrescription :=
  circuitRawGatePrescription (circuitGateKey pointKey inputKey)
    (circuitSourceSlope source) lifts (circuitSourceTable source)

/-- This event retains every complete hash lift in the actual circuit. -/
def CircuitHashMatches (pointKey inputKey : InputMacKey) (lifts : RawCircuitGate → FullHashLift)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : Prop :=
  ∀ gate, fixedDaviesMeyerHashLift (rawCircuitLocation gate) (rawCircuitWindow gate)
    (circuitGateKey pointKey inputKey gate).falseLabel oracle = lifts gate

private theorem digitGarble_table_get (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (key : CoordinateMacKey) (bit : Fin coordinateBitCount) :
    ((DigitAdaptor.garble windows slope key).1).get bit =
      (BitAdaptor.garble (windows bit.val) slope (key.get bit)).1 := by
  simp [DigitAdaptor.garble]

section ActualSource

variable (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey mask r1 r2 : BaseField) (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (pointKey inputKey : InputMacKey) (quotients : CircuitMaskQuotients)

/-- The source field projection equals the actual false-label hash value. -/
theorem actualCircuitMaskSample_field (gate : RawCircuitGate) :
    circuitSourceField (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey quotients) gate =
    (Pipeline.fixedKeyGate oracle (rawCircuitLocation gate) (rawCircuitWindow gate)).hashToField
      (circuitGateKey pointKey inputKey gate).falseLabel := by
  simp only [circuitSourceField, actualCircuitMaskSample, actualCurveMaskSample,
    actualRowMaskSample, actualXMaskSample, actualYMaskSample, actualZMaskSample,
    curveMaskSource, xMaskSource, yMaskSource, zMaskSource, Pipeline.pointOracles,
    Vector.get_ofFn, Pipeline.curveOracles, Pipeline.biquadraticOracles]
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;>
      fin_cases adaptor <;> rfl

/-- The source table projection uses the actual mask-dependent slope. -/
theorem actualCircuitMaskSample_gateTable (gate : RawCircuitGate) :
    let source := actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey quotients
    circuitSourceTable source gate =
      (BitAdaptor.garble (Pipeline.fixedKeyGate oracle (rawCircuitLocation gate) (rawCircuitWindow gate))
        (circuitSourceSlope source gate) (circuitGateKey pointKey inputKey gate)).1 := by
  dsimp only
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor
    all_goals
      simp [circuitSourceTable, circuitSourceSlope, actualCircuitMaskSample, actualCurveMaskSample,
        curveMaskSource, Pipeline.curveOracles, CurveMembership.garble,
        digitGarble_bitsK_eq, digitGarble_table_get,
        rawCircuitLocation, rawCircuitWindow, circuitGateKey]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> fin_cases adaptor
    all_goals
      simp [circuitSourceTable, circuitSourceSlope, actualCircuitMaskSample,
        actualRowMaskSample, actualXMaskSample, actualYMaskSample, actualZMaskSample,
        xMaskSource, yMaskSource, zMaskSource, Pipeline.pointOracles,
        Vector.get_ofFn, Pipeline.biquadraticOracles,
        Biquadratic.garbleX, Biquadratic.garbleY, Biquadratic.garbleZ,
        digitGarble_bitsK_eq, Option.getD_some, digitGarble_table_get, rawCircuitLocation, rawCircuitWindow, circuitGateKey]

end ActualSource

/-- This condition compares every field randomizer and hash mask. -/
def CircuitSourceDataEq (first second : CircuitMaskSample) : Prop :=
  first.1.1 = second.1.1 ∧ ∀ row,
    (first.2 row).1.1 = (second.2 row).1.1 ∧
    (first.2 row).2.1.1 = (second.2 row).2.1.1 ∧
    (first.2 row).2.2.1 = (second.2 row).2.2.1

/-- Equal source data gives each later adaptor the same slope. -/
theorem circuitSourceSlope_eq_of_data {first second : CircuitMaskSample}
    (equal : CircuitSourceDataEq first second) : circuitSourceSlope first = circuitSourceSlope second := by
  funext gate
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · simp only [circuitSourceSlope, equal.1]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩)
    · simp only [circuitSourceSlope, (equal.2 row).1]
    · simp only [circuitSourceSlope, (equal.2 row).2.1]
    · simp only [circuitSourceSlope, (equal.2 row).2.2]

private theorem maskSample_ext {randomizers adaptors : Nat}
    {first second : ((Fin randomizers → BaseField) ×
      (Fin adaptors → Fin coordinateBitCount → BaseField)) × BiquadraticSampleRemainder adaptors}
    (data : first.1 = second.1)
    (tables : ∀ adaptor bit, (first.2.1 adaptor).get bit = (second.2.1 adaptor).get bit)
    (quotients : first.2.2 = second.2.2) : first = second := by
  apply Prod.ext data
  apply Prod.ext _ quotients
  funext adaptor
  apply Vector.ext
  intro bit valid
  exact tables adaptor ⟨bit, valid⟩

/-- The flat ciphertext projection and source data retain the whole sample. -/
theorem circuitSource_ext {first second : CircuitMaskSample}
    (data : CircuitSourceDataEq first second)
    (tables : circuitSourceTable first = circuitSourceTable second)
    (quotients : circuitSourceQuotients first = circuitSourceQuotients second) : first = second := by
  apply Prod.ext
  · exact maskSample_ext data.1 (fun adaptor bit => congrFun tables (.inl (adaptor, bit)))
      (congrArg Prod.fst quotients)
  · funext row
    apply Prod.ext
    · exact maskSample_ext (data.2 row).1
        (fun adaptor bit => congrFun tables (.inr (row, .inl (adaptor, bit))))
        (congrArg (fun value : CircuitMaskQuotients => (value.2 row).1) quotients)
    · apply Prod.ext
      · exact maskSample_ext (data.2 row).2.1
          (fun adaptor bit => congrFun tables (.inr (row, .inr (.inl (adaptor, bit)))))
          (congrArg (fun value : CircuitMaskQuotients => (value.2 row).2.1) quotients)
      · exact maskSample_ext (data.2 row).2.2
          (fun adaptor bit => congrFun tables (.inr (row, .inr (.inr (adaptor, bit)))))
          (congrArg (fun value : CircuitMaskQuotients => (value.2 row).2.2) quotients)

section SourceEvent

variable (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey mask r1 r2 : BaseField) (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (pointKey inputKey : InputMacKey) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))

include randomizers residues

/-- Complete hash agreement fixes all source data before any table constraints. -/
theorem actualCircuitMaskSample_data_of_hash
    (hashes : CircuitHashMatches pointKey inputKey lifts oracle) :
    CircuitSourceDataEq (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey (circuitSourceQuotients source)) source := by
  have fields : ∀ gate, circuitSourceField
      (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
        oracle pointKey inputKey (circuitSourceQuotients source)) gate = circuitSourceField source gate := by
    intro gate
    rw [actualCircuitMaskSample_field, residues]
    exact fixedHashToField_of_lift oracle _ _ _ _ (hashes gate)
  constructor
  · exact Prod.ext randomizers.1.symm (funext fun adaptor => funext fun bit => fields (.inl (adaptor, bit)))
  · intro row
    refine ⟨?_, ?_, ?_⟩
    · exact Prod.ext (randomizers.2 row).1.symm
        (funext fun adaptor => funext fun bit => fields (.inr (row, .inl (adaptor, bit))))
    · exact Prod.ext (randomizers.2 row).2.1.symm
        (funext fun adaptor => funext fun bit => fields (.inr (row, .inr (.inl (adaptor, bit)))))
    · exact Prod.ext (randomizers.2 row).2.2.symm
        (funext fun adaptor => funext fun bit => fields (.inr (row, .inr (.inr (adaptor, bit)))))

/-- The actual complete source event is exactly the prescribed raw gate event. -/
theorem rawGarblingMatches_iff_actualSource :
    RawGarblingMatches (sourceGatePrescription source pointKey inputKey lifts) oracle ↔
      CircuitHashMatches pointKey inputKey lifts oracle ∧
      actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
        oracle pointKey inputKey (circuitSourceQuotients source) = source := by
  constructor
  · intro matching
    have hashes : CircuitHashMatches pointKey inputKey lifts oracle := fun gate => (matching gate).1
    have data := actualCircuitMaskSample_data_of_hash outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey source lifts randomizers residues hashes
    refine ⟨hashes, circuitSource_ext data ?_ rfl⟩
    funext gate
    rw [actualCircuitMaskSample_gateTable, circuitSourceSlope_eq_of_data data]
    exact (matching gate).2
  · rintro ⟨hashes, sourceEqual⟩ gate
    refine ⟨hashes gate, ?_⟩
    have table := actualCircuitMaskSample_gateTable outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey (circuitSourceQuotients source) gate
    dsimp only at table
    rw [sourceEqual] at table
    exact table.symm

end SourceEvent

/-- This map reads every ciphertext from the complete public pipeline table. -/
def pipelineGateTable (table : Pipeline.Table) : RawCircuitGate → BitAdaptor.Table
  | .inl (adaptor, bit) =>
      (![table.curve.x3, table.curve.x5, table.curve.x7, table.curve.y4, table.curve.y6] adaptor).get bit
  | .inr (row, .inl (adaptor, bit)) =>
      let part := table.pointMAC.x.get row
      ((![part.y6, part.y8, part.y10, part.x9] adaptor).getD
        (Vector.replicate coordinateBitCount defaultBitAdaptorTable)).get bit
  | .inr (row, .inr (.inl (adaptor, bit))) =>
      let part := table.pointMAC.y.get row
      ((![part.y6, part.x7, part.x9] adaptor).getD
        (Vector.replicate coordinateBitCount defaultBitAdaptorTable)).get bit
  | .inr (row, .inr (.inr (adaptor, bit))) =>
      let part := table.pointMAC.z.get row
      ((![part.y6, part.y8, part.y10, part.x7, part.x9] adaptor).getD
        (Vector.replicate coordinateBitCount defaultBitAdaptorTable)).get bit

/-- This table retains every public coefficient from the prescribed source. -/
def circuitSourcePipelineTable (bridgeKey mask : BaseField)
    (rows : Vector Coordinates.Rows FieldMacToECMac.outputMacCount) (input : AffineInput)
    (source : CircuitMaskSample) : Pipeline.Table :=
  let sample := circuitMaskSampleGarble bridgeKey mask rows input source
  ⟨sample.curveRequest.table, pointGateTable sample.pointRequests⟩

/-- The assembled table retains each source ciphertext exactly. -/
theorem circuitSourcePipelineTable_gate (bridgeKey mask : BaseField)
    (rows : Vector Coordinates.Rows FieldMacToECMac.outputMacCount) (input : AffineInput)
    (source : CircuitMaskSample) (gate : RawCircuitGate) :
    pipelineGateTable (circuitSourcePipelineTable bridgeKey mask rows input source) gate =
      circuitSourceTable source gate := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;>
      simp [pipelineGateTable, circuitSourcePipelineTable, circuitSourceTable,
        circuitMaskSampleGarble, PublicSample.curveRequest, curveMaskSampleGarble,
        curveSampleViewEquiv, CurvePublicSample.request, CurveGateRequest.table]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> fin_cases adaptor
    all_goals
      simp [pipelineGateTable, circuitSourcePipelineTable, circuitSourceTable,
        circuitMaskSampleGarble, PublicSample.pointRequests, pointGateTable,
        rowMaskSampleGarble, RowPublicSample.request, BiquadraticRowRequest.table,
        xMaskSampleGarble, yMaskSampleGarble, zMaskSampleGarble,
        xSampleViewEquiv, ySampleViewEquiv, zSampleViewEquiv,
        XPublicSample.request, YPublicSample.request, ZPublicSample.request,
        BiquadraticXRequest.table, BiquadraticYRequest.table, BiquadraticZRequest.table]

/-- The raw constraints equal the actual complete pipeline view and hash tape. -/
theorem rawGarblingMatches_iff_pipeline (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey r1 r2 : BaseField)
    (mask : NonZeroBase) (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (input : AffineInput) (source : CircuitMaskSample)
    (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField)) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    RawGarblingMatches (sourceGatePrescription source pointKey inputKey lifts) oracle ↔
      CircuitHashMatches pointKey inputKey lifts oracle ∧
      Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2 oracle encOracle hashOracle inputKey =
        circuitSourcePipelineTable bridgeKey mask.value
          (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input source := by
  dsimp only
  let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
  let actual := actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask.value r1 r2
    oracle pointKey inputKey (circuitSourceQuotients source)
  have assembled : circuitSourcePipelineTable bridgeKey mask.value
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input actual =
      Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2 oracle encOracle hashOracle inputKey :=
    actualCircuitMaskSample_pipelineTable outputKeys pointRandomness bridgeKey r1 r2 mask oracle
      encOracle hashOracle inputKey (circuitSourceQuotients source) input
  rw [rawGarblingMatches_iff_actualSource outputKeys pointRandomness bridgeKey mask.value r1 r2
    oracle pointKey inputKey source lifts randomizers residues]
  apply and_congr_right
  intro hashes
  change actual = source ↔ _
  constructor
  · intro equal
    rw [← assembled, equal]
  · intro equal
    apply circuitSource_ext
    · exact actualCircuitMaskSample_data_of_hash outputKeys pointRandomness bridgeKey mask.value r1 r2
        oracle pointKey inputKey source lifts randomizers residues hashes
    · funext gate
      rw [← circuitSourcePipelineTable_gate bridgeKey mask.value
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input actual,
        assembled, equal, circuitSourcePipelineTable_gate]
    · rfl

end
end Kriterion.ArgoMAC.Security
