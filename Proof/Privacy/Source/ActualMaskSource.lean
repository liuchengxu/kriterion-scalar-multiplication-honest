import Proof.Privacy.Distribution.CircuitMaskDistribution
import Proof.Privacy.Programming.GarblingConstraints

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- This sample extracts the actual X masks and ciphertext rows. -/
def actualXMaskSample (row : Coordinates.Coefficients) (randomness : Biquadratic.XRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 4 → Fin coordinateBitCount → HashLiftQuotient) : XMaskSample :=
  let table := Biquadratic.garbleX row.constant row.x row.y row.xy row.ySquared randomness oracles key
  let empty := Vector.replicate coordinateBitCount defaultBitAdaptorTable
  (xMaskSource randomness oracles key,
    (![table.y6.getD empty, table.y8.getD empty, table.y10.getD empty, table.x9.getD empty], quotients))

/-- The extracted X sample reconstructs the actual public table. -/
theorem actualXMaskSample_table (row : Coordinates.Coefficients)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 4 → Fin coordinateBitCount → HashLiftQuotient) (input : AffineInput) :
    (xMaskSampleGarble row input (actualXMaskSample row randomness oracles key quotients)).request.table =
      Biquadratic.garbleX row.constant row.x row.y row.xy row.ySquared randomness oracles key := by
  dsimp only [xMaskSampleGarble, actualXMaskSample, xSampleViewEquiv, Equiv.symm,
    Equiv.coe_fn_mk, XPublicSample.request, BiquadraticXRequest.table]
  rw [xMaskGarbleEquiv_coefficients,
    ← garbleX_maskCoefficients row.constant ![row.x, row.y, row.xy, row.ySquared] randomness oracles key]
  rfl

/-- This sample extracts the actual Y masks and ciphertext rows. -/
def actualYMaskSample (row : Coordinates.Coefficients) (randomness : Biquadratic.YRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 3 → Fin coordinateBitCount → HashLiftQuotient) : YMaskSample :=
  let table := Biquadratic.garbleY row.constant row.x row.xSquared row.ySquared randomness oracles key
  let empty := Vector.replicate coordinateBitCount defaultBitAdaptorTable
  (yMaskSource randomness oracles key,
    (![table.y6.getD empty, table.x7.getD empty, table.x9.getD empty], quotients))

/-- The extracted Y sample reconstructs the actual public table. -/
theorem actualYMaskSample_table (row : Coordinates.Coefficients)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 3 → Fin coordinateBitCount → HashLiftQuotient) (input : AffineInput) :
    (yMaskSampleGarble row input (actualYMaskSample row randomness oracles key quotients)).request.table =
      Biquadratic.garbleY row.constant row.x row.xSquared row.ySquared randomness oracles key := by
  dsimp only [yMaskSampleGarble, actualYMaskSample, ySampleViewEquiv, Equiv.symm,
    Equiv.coe_fn_mk, YPublicSample.request, BiquadraticYRequest.table]
  rw [yMaskGarbleEquiv_coefficients,
    ← garbleY_maskCoefficients row.constant ![row.x, row.xSquared, row.ySquared] randomness oracles key]
  rfl

/-- This sample extracts the actual Z masks and ciphertext rows. -/
def actualZMaskSample (row : Coordinates.Coefficients) (randomness : Biquadratic.ZRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) : ZMaskSample :=
  let table := Biquadratic.garbleZ row.constant row.y row.xy row.xSquared row.ySquared randomness oracles key
  let empty := Vector.replicate coordinateBitCount defaultBitAdaptorTable
  (zMaskSource randomness oracles key,
    (![table.y6.getD empty, table.y8.getD empty, table.y10.getD empty, table.x7.getD empty,
      table.x9.getD empty], quotients))

/-- The extracted Z sample reconstructs the actual public table. -/
theorem actualZMaskSample_table (row : Coordinates.Coefficients)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) (input : AffineInput) :
    (zMaskSampleGarble row input (actualZMaskSample row randomness oracles key quotients)).request.table =
      Biquadratic.garbleZ row.constant row.y row.xy row.xSquared row.ySquared randomness oracles key := by
  dsimp only [zMaskSampleGarble, actualZMaskSample, zSampleViewEquiv, Equiv.symm,
    Equiv.coe_fn_mk, ZPublicSample.request, BiquadraticZRequest.table]
  rw [zMaskGarbleEquiv_coefficients,
    ← garbleZ_maskCoefficients row.constant ![row.y, row.xy, row.xSquared, row.ySquared] randomness oracles key]
  rfl

/-- This sample extracts the actual curve masks and ciphertext rows. -/
def actualCurveMaskSample (bridgeKey mask r1 r2 : BaseField)
    (oracles : CurveMembership.Oracles) (key : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) : CurveMaskSample :=
  let table := CurveMembership.garble bridgeKey mask r1 r2 oracles key
  (curveMaskSource r1 r2 oracles key,
    (![table.x3, table.x5, table.x7, table.y4, table.y6], quotients))

/-- The extracted curve sample reconstructs the actual public table. -/
theorem actualCurveMaskSample_table (bridgeKey mask r1 r2 : BaseField)
    (oracles : CurveMembership.Oracles) (key : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) (input : AffineInput) :
    (curveMaskSampleGarble bridgeKey mask input
      (actualCurveMaskSample bridgeKey mask r1 r2 oracles key quotients)).request.table =
        CurveMembership.garble bridgeKey mask r1 r2 oracles key := by
  dsimp only [curveMaskSampleGarble, actualCurveMaskSample, curveSampleViewEquiv, Equiv.symm,
    Equiv.coe_fn_mk, CurvePublicSample.request, CurveGateRequest.table]
  rw [← garble_curveMaskCoefficients bridgeKey mask r1 r2 oracles key input]
  rfl

/-- These quotients retain one complete hash fiber for each bit adaptor. -/
abbrev RowMaskQuotients :=
  (Fin 4 → Fin coordinateBitCount → HashLiftQuotient) ×
  (Fin 3 → Fin coordinateBitCount → HashLiftQuotient) ×
  (Fin 5 → Fin coordinateBitCount → HashLiftQuotient)

abbrev CircuitMaskQuotients :=
  (Fin 5 → Fin coordinateBitCount → HashLiftQuotient) ×
  (Fin FieldMacToECMac.outputMacCount → RowMaskQuotients)

/-- This sample extracts all three actual coordinate masks and their public rows. -/
def actualRowMaskSample (rows : Coordinates.Rows) (randomness : FieldMacToECMac.RowRandomness)
    (oracles : FieldMacToECMac.RowOracles) (key : InputMacKey)
    (quotients : RowMaskQuotients) : RowMaskSample :=
  (actualXMaskSample rows.x randomness.x oracles.x key quotients.1,
    actualYMaskSample rows.y randomness.y oracles.y key quotients.2.1,
    actualZMaskSample rows.z randomness.z oracles.z key quotients.2.2)

/-- The extracted row sample reconstructs the actual three-coordinate table. -/
theorem actualRowMaskSample_table (rows : Coordinates.Rows)
    (randomness : FieldMacToECMac.RowRandomness) (oracles : FieldMacToECMac.RowOracles)
    (key : InputMacKey) (quotients : RowMaskQuotients) (input : AffineInput) :
    (rowMaskSampleGarble rows input (actualRowMaskSample rows randomness oracles key quotients)).request.table =
      FieldMacToECMac.garbleRow rows randomness oracles key := by
  dsimp only [actualRowMaskSample, rowMaskSampleGarble, RowPublicSample.request,
    BiquadraticRowRequest.table]
  rw [actualXMaskSample_table, actualYMaskSample_table, actualZMaskSample_table]
  rfl

/-- This sample extracts the actual whole-circuit masks and public rows. -/
def actualCircuitMaskSample (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey mask r1 r2 : BaseField)
    (fixedOracle : Cryptography.PermutationOracle Pipeline.FixedKeyIndex Cryptography.Block)
    (pointKey inputKey : InputMacKey) (quotients : CircuitMaskQuotients) : CircuitMaskSample :=
  (actualCurveMaskSample bridgeKey mask r1 r2 (Pipeline.curveOracles fixedOracle) inputKey quotients.1,
    fun index => actualRowMaskSample
      ((FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness).get index)
      (pointRandomness.get index) ((Pipeline.pointOracles fixedOracle).get index)
      pointKey (quotients.2 index))

private theorem pointGateTable_eq_rows (requests : PointGateRequests)
    (rows : Vector FieldMacToECMac.RowTable FieldMacToECMac.outputMacCount)
    (equal : ∀ index, (requests.get index).table = rows.get index) :
    pointGateTable requests =
      ⟨rows.map FieldMacToECMac.RowTable.x, rows.map FieldMacToECMac.RowTable.y,
        rows.map FieldMacToECMac.RowTable.z⟩ := by
  have xEqual : Vector.ofFn (fun index => (requests.get index).table.x) =
      rows.map FieldMacToECMac.RowTable.x := by
    apply Vector.ext
    intro index valid
    simp only [Vector.getElem_ofFn, Vector.getElem_map]
    change (requests.get ⟨index, valid⟩).table.x = (rows.get ⟨index, valid⟩).x
    rw [equal]
  have yEqual : Vector.ofFn (fun index => (requests.get index).table.y) =
      rows.map FieldMacToECMac.RowTable.y := by
    apply Vector.ext
    intro index valid
    simp only [Vector.getElem_ofFn, Vector.getElem_map]
    change (requests.get ⟨index, valid⟩).table.y = (rows.get ⟨index, valid⟩).y
    rw [equal]
  have zEqual : Vector.ofFn (fun index => (requests.get index).table.z) =
      rows.map FieldMacToECMac.RowTable.z := by
    apply Vector.ext
    intro index valid
    simp only [Vector.getElem_ofFn, Vector.getElem_map]
    change (requests.get ⟨index, valid⟩).table.z = (rows.get ⟨index, valid⟩).z
    rw [equal]
  unfold pointGateTable
  rw [xEqual, yEqual, zEqual]

/-- The extracted circuit sample reconstructs the actual point-layer table. -/
theorem actualCircuitMaskSample_pointTable (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey mask r1 r2 : BaseField)
    (fixedOracle : Cryptography.PermutationOracle Pipeline.FixedKeyIndex Cryptography.Block)
    (pointKey inputKey : InputMacKey) (quotients : CircuitMaskQuotients) (input : AffineInput) :
    pointGateTable (circuitMaskSampleGarble bridgeKey mask
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input
      (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
        fixedOracle pointKey inputKey quotients)).pointRequests =
      FieldMacToECMac.garble (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness)
        pointRandomness (Pipeline.pointOracles fixedOracle) pointKey := by
  apply pointGateTable_eq_rows
  intro index
  simp only [circuitMaskSampleGarble, PublicSample.pointRequests, actualCircuitMaskSample,
    Vector.get_map, Vector.get_ofFn]
  exact actualRowMaskSample_table _ _ _ pointKey _ input

/-- The extracted source reconstructs the actual linked pipeline table. -/
theorem actualCircuitMaskSample_pipelineTable (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey r1 r2 : BaseField)
    (mask : NonZeroBase)
    (fixedOracle : Cryptography.PermutationOracle Pipeline.FixedKeyIndex Cryptography.Block)
    (encOracle : Cryptography.PermutationOracle EncPRF.PermutationIndex Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey)
    (quotients : CircuitMaskQuotients) (input : AffineInput) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    let sample := circuitMaskSampleGarble bridgeKey mask.value
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input
      (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask.value r1 r2
        fixedOracle pointKey inputKey quotients)
    (⟨sample.curveRequest.table, pointGateTable sample.pointRequests⟩ : Pipeline.Table) =
      Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2
        fixedOracle encOracle hashOracle inputKey := by
  dsimp only
  rw [actualCircuitMaskSample_pointTable]
  change (⟨(curveMaskSampleGarble bridgeKey mask.value input
      (actualCurveMaskSample bridgeKey mask.value r1 r2
        (Pipeline.curveOracles fixedOracle) inputKey quotients.1)).request.table, _⟩ : Pipeline.Table) = _
  rw [actualCurveMaskSample_table]
  rfl

end

end Kriterion.ArgoMAC.Security
