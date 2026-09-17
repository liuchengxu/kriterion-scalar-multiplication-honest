/- This file transports the independent field masks through all circuit rows. -/

import Proof.Privacy.Distribution.CurveDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

attribute [local instance] bitAdaptorTableFintype publicVectorFintype ciphertextFintype

/-- This equivalence separates the old result and keeps the sample remainder. -/
def maskSampleSplitEquiv {Sample View Source Remainder : Type}
    (view : Sample ≃ View × Remainder)
    (result : View → BaseField) (shift : BaseField → View → View)
    (shiftZero : ∀ value, shift 0 value = value)
    (shiftAdd : ∀ a b value, shift a (shift b value) = shift (a + b) value)
    (resultShift : ∀ a value, result (shift a value) = result value + a)
    (target : BaseField) (garble : Source ≃ {value // result value = target}) :
    Sample ≃ BaseField × (Source × Remainder) :=
  view.trans ((Equiv.prodCongr
    (resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target)
    (Equiv.refl Remainder)).trans
      ((Equiv.prodAssoc _ _ _).trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr garble.symm (Equiv.refl _)))))

/-- This identity keeps the remainder and retargets only the mask view. -/
theorem maskSampleSplitEquiv_selected {Sample View Source Remainder : Type}
    (view : Sample ≃ View × Remainder)
    (result : View → BaseField) (shift : BaseField → View → View)
    (shiftZero : ∀ value, shift 0 value = value)
    (shiftAdd : ∀ a b value, shift a (shift b value) = shift (a + b) value)
    (resultShift : ∀ a value, result (shift a value) = result value + a)
    (target : BaseField) (garble : Source ≃ {value // result value = target})
    (sample : Sample) :
    let source := (maskSampleSplitEquiv view result shift shiftZero shiftAdd
      resultShift target garble sample).2
    view.symm ((garble source.1).1, source.2) =
      view.symm (shift (target - result (view sample).1) (view sample).1,
        (view sample).2) := by
  change view.symm ((garble (garble.symm
    ((resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target)
      (view sample).1).2)).1, (view sample).2) = _
  rw [garble.apply_symm_apply]
  rfl

abbrev XMaskSample := XMaskData × BiquadraticSampleRemainder 4
abbrev YMaskSample := YMaskData × BiquadraticSampleRemainder 3
abbrev ZMaskSample := ZMaskData × BiquadraticSampleRemainder 5
abbrev CurveMaskSample := CurveMaskData × BiquadraticSampleRemainder 5
abbrev RowMaskSample := XMaskSample × YMaskSample × ZMaskSample
abbrev CircuitMaskSample := CurveMaskSample × (Fin FieldMacToECMac.outputMacCount → RowMaskSample)
abbrev CircuitMaskResults := BaseField × (Fin FieldMacToECMac.outputMacCount → BaseField × BaseField × BaseField)

local instance xMaskSampleFintype : Fintype XMaskSample := inferInstance
local instance yMaskSampleFintype : Fintype YMaskSample := inferInstance
local instance zMaskSampleFintype : Fintype ZMaskSample := inferInstance
local instance curveMaskSampleFintype : Fintype CurveMaskSample := inferInstance
local instance rowMaskSampleFintype : Fintype RowMaskSample := inferInstance
local instance circuitMaskSampleFintype : Fintype CircuitMaskSample := inferInstance

def xMaskSampleSplit (row : Coordinates.Coefficients) (input : AffineInput) :
    XPublicSample ≃ BaseField × XMaskSample :=
  maskSampleSplitEquiv xSampleViewEquiv (xMaskResult input) xMaskPivotShift
    xMaskPivotShift_zero xMaskPivotShift_add (xMaskResult_pivotShift input)
    (xMaskPolynomial row.constant ![row.x, row.y, row.xy, row.ySquared] input)
    (xMaskGarbleEquiv row.constant ![row.x, row.y, row.xy, row.ySquared] input)

def yMaskSampleSplit (row : Coordinates.Coefficients) (input : AffineInput) :
    YPublicSample ≃ BaseField × YMaskSample :=
  maskSampleSplitEquiv ySampleViewEquiv (yMaskResult input) yMaskPivotShift
    yMaskPivotShift_zero yMaskPivotShift_add (yMaskResult_pivotShift input)
    (yMaskPolynomial row.constant ![row.x, row.xSquared, row.ySquared] input)
    (yMaskGarbleEquiv row.constant ![row.x, row.xSquared, row.ySquared] input)

def zMaskSampleSplit (row : Coordinates.Coefficients) (input : AffineInput) :
    ZPublicSample ≃ BaseField × ZMaskSample :=
  maskSampleSplitEquiv zSampleViewEquiv (zMaskResult input) zMaskPivotShift
    zMaskPivotShift_zero zMaskPivotShift_add (zMaskResult_pivotShift input)
    (zMaskPolynomial row.constant ![row.y, row.xy, row.xSquared, row.ySquared] input)
    (zMaskGarbleEquiv row.constant ![row.y, row.xy, row.xSquared, row.ySquared] input)

def curveMaskSampleSplit (bridgeKey mask : BaseField) (input : AffineInput) :
    CurvePublicSample ≃ BaseField × CurveMaskSample :=
  maskSampleSplitEquiv curveSampleViewEquiv (curveMaskResult input) curveMaskPivot
    curveMaskPivot_zero curveMaskPivot_add (curveMaskResult_pivot input)
    (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2))
    (curveMaskViewEquiv bridgeKey mask input)

/-- This sample update keeps every table and quotient. -/
def XPublicSample.retargetMask (sample : XPublicSample)
    (input : AffineInput) (target : BaseField) : XPublicSample :=
  { sample with
    targets := Function.update sample.targets 3
      (retargetBits (sample.targets 3)
        (target - sample.request.result input + DigitAdaptor.fromBits (sample.targets 3))) }

@[simp] theorem XPublicSample.retargetMask_request (sample : XPublicSample)
    (input : AffineInput) (target : BaseField) :
    (sample.retargetMask input target).request = sample.request.retarget input target := by
  rfl

private theorem xSample_result (sample : XPublicSample) (input : AffineInput) :
    xMaskResult input (xSampleViewEquiv sample).1 = sample.request.result input := by
  simp [xMaskResult, xMaskRest, xSampleViewEquiv, XPublicSample.request,
    BiquadraticXRequest.result]
  ring

private theorem xSample_pivot (sample : XPublicSample)
    (input : AffineInput) (target : BaseField) :
    xSampleViewEquiv.symm (xMaskPivotShift (target - xMaskResult input (xSampleViewEquiv sample).1)
      (xSampleViewEquiv sample).1, (xSampleViewEquiv sample).2) = sample.retargetMask input target := by
  rw [xSample_result]
  unfold xMaskPivotShift xSampleViewEquiv XPublicSample.retargetMask
  dsimp
  rw [lowMaskShift_eq_retargetBits]
  rw [add_comm (DigitAdaptor.fromBits _) (target - sample.request.result input)]

/-- This sample update keeps every table and quotient. -/
def YPublicSample.retargetMask (sample : YPublicSample)
    (input : AffineInput) (target : BaseField) : YPublicSample :=
  { sample with
    targets := Function.update sample.targets 2
      (retargetBits (sample.targets 2)
        (target - sample.request.result input + DigitAdaptor.fromBits (sample.targets 2))) }

@[simp] theorem YPublicSample.retargetMask_request (sample : YPublicSample)
    (input : AffineInput) (target : BaseField) :
    (sample.retargetMask input target).request = sample.request.retarget input target := by
  rfl

private theorem ySample_result (sample : YPublicSample) (input : AffineInput) :
    yMaskResult input (ySampleViewEquiv sample).1 = sample.request.result input := by
  simp [yMaskResult, yMaskRest, ySampleViewEquiv, YPublicSample.request,
    BiquadraticYRequest.result]
  ring

private theorem ySample_pivot (sample : YPublicSample)
    (input : AffineInput) (target : BaseField) :
    ySampleViewEquiv.symm (yMaskPivotShift (target - yMaskResult input (ySampleViewEquiv sample).1)
      (ySampleViewEquiv sample).1, (ySampleViewEquiv sample).2) = sample.retargetMask input target := by
  rw [ySample_result]
  unfold yMaskPivotShift ySampleViewEquiv YPublicSample.retargetMask
  dsimp
  rw [lowMaskShift_eq_retargetBits]
  rw [add_comm (DigitAdaptor.fromBits _) (target - sample.request.result input)]

/-- This sample update keeps every table and quotient. -/
def ZPublicSample.retargetMask (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField) : ZPublicSample :=
  { sample with
    targets := Function.update sample.targets 4
      (retargetBits (sample.targets 4)
        (target - sample.request.result input + DigitAdaptor.fromBits (sample.targets 4))) }

@[simp] theorem ZPublicSample.retargetMask_request (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField) :
    (sample.retargetMask input target).request = sample.request.retarget input target := by
  rfl

private theorem zSample_result (sample : ZPublicSample) (input : AffineInput) :
    zMaskResult input (zSampleViewEquiv sample).1 = sample.request.result input := by
  simp [zMaskResult, zMaskRest, zSampleViewEquiv, ZPublicSample.request,
    BiquadraticZRequest.result]
  ring

private theorem zSample_pivot (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField) :
    zSampleViewEquiv.symm (zMaskPivotShift (target - zMaskResult input (zSampleViewEquiv sample).1)
      (zSampleViewEquiv sample).1, (zSampleViewEquiv sample).2) = sample.retargetMask input target := by
  rw [zSample_result]
  unfold zMaskPivotShift zSampleViewEquiv ZPublicSample.retargetMask
  dsimp
  rw [lowMaskShift_eq_retargetBits]
  rw [add_comm (DigitAdaptor.fromBits _) (target - sample.request.result input)]

/-- This sample update keeps every table and quotient. -/
def CurvePublicSample.retargetMask (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) : CurvePublicSample :=
  { sample with
    targets := Function.update sample.targets 2
      (retargetBits (sample.targets 2)
        (target - sample.request.result input + DigitAdaptor.fromBits (sample.targets 2))) }

@[simp] theorem CurvePublicSample.retargetMask_request (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) :
    (sample.retargetMask input target).request = sample.request.retarget input target := by
  rfl

private theorem curveSample_result (sample : CurvePublicSample) (input : AffineInput) :
    curveMaskResult input (curveSampleViewEquiv sample).1 = sample.request.result input := by
  simp [curveMaskResult, curveMaskRest, curveSampleViewEquiv, CurvePublicSample.request,
    CurveGateRequest.result]
  ring

private theorem curveSample_pivot (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) :
    curveSampleViewEquiv.symm (curveMaskPivot (target - curveMaskResult input (curveSampleViewEquiv sample).1)
      (curveSampleViewEquiv sample).1, (curveSampleViewEquiv sample).2) = sample.retargetMask input target := by
  rw [curveSample_result]
  unfold curveMaskPivot curveSampleViewEquiv CurvePublicSample.retargetMask
  dsimp
  rw [lowMaskShift_eq_retargetBits]
  rw [add_comm (DigitAdaptor.fromBits _) (target - sample.request.result input)]

/-- This equivalence separates the three old coordinate results in one row. -/
def rowMaskSampleSplit (rows : Coordinates.Rows) (input : AffineInput) :
    RowPublicSample ≃ (BaseField × BaseField × BaseField) × RowMaskSample where
  toFun sample :=
    let x := xMaskSampleSplit rows.x input sample.x
    let y := yMaskSampleSplit rows.y input sample.y
    let z := zMaskSampleSplit rows.z input sample.z
    ((x.1, y.1, z.1), (x.2, y.2, z.2))
  invFun pair := {
    x := (xMaskSampleSplit rows.x input).symm (pair.1.1, pair.2.1)
    y := (yMaskSampleSplit rows.y input).symm (pair.1.2.1, pair.2.2.1)
    z := (zMaskSampleSplit rows.z input).symm (pair.1.2.2, pair.2.2.2) }
  left_inv sample := by simp
  right_inv pair := by simp

private def functionPairEquiv {Index A B : Type} :
    (Index → A × B) ≃ (Index → A) × (Index → B) where
  toFun values := (fun index => (values index).1, fun index => (values index).2)
  invFun pair index := (pair.1 index, pair.2 index)
  left_inv _ := rfl
  right_inv _ := rfl

private def publicSamplePartsEquiv : PublicSample ≃
    CurvePublicSample × (Fin FieldMacToECMac.outputMacCount → RowPublicSample) where
  toFun sample := (sample.curve, vectorFunctionEquiv.symm sample.points)
  invFun pair := { curve := pair.1, points := vectorFunctionEquiv pair.2 }
  left_inv sample := by simp
  right_inv pair := by simp

/-- This equivalence separates all 274 old results from the circuit mask source. -/
def circuitMaskSampleSplit (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) :
    PublicSample ≃ CircuitMaskResults × CircuitMaskSample :=
  publicSamplePartsEquiv.trans ((Equiv.prodCongr
    (curveMaskSampleSplit bridgeKey mask input)
    ((Equiv.piCongrRight fun index => rowMaskSampleSplit (rows.get index) input).trans
      functionPairEquiv)).trans (Equiv.prodProdProdComm _ _ _ _))

/-- This sample contains the real public coefficients and selected targets. -/
def xMaskSampleGarble (row : Coordinates.Coefficients) (input : AffineInput)
    (source : XMaskSample) : XPublicSample :=
  xSampleViewEquiv.symm ((xMaskGarbleEquiv row.constant
    ![row.x, row.y, row.xy, row.ySquared] input source.1).1, source.2)

def yMaskSampleGarble (row : Coordinates.Coefficients) (input : AffineInput)
    (source : YMaskSample) : YPublicSample :=
  ySampleViewEquiv.symm ((yMaskGarbleEquiv row.constant
    ![row.x, row.xSquared, row.ySquared] input source.1).1, source.2)

def zMaskSampleGarble (row : Coordinates.Coefficients) (input : AffineInput)
    (source : ZMaskSample) : ZPublicSample :=
  zSampleViewEquiv.symm ((zMaskGarbleEquiv row.constant
    ![row.y, row.xy, row.xSquared, row.ySquared] input source.1).1, source.2)

def curveMaskSampleGarble (bridgeKey mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) : CurvePublicSample :=
  curveSampleViewEquiv.symm ((curveMaskViewEquiv bridgeKey mask input source.1).1, source.2)

def rowMaskSampleGarble (rows : Coordinates.Rows) (input : AffineInput)
    (source : RowMaskSample) : RowPublicSample := {
  x := xMaskSampleGarble rows.x input source.1
  y := yMaskSampleGarble rows.y input source.2.1
  z := zMaskSampleGarble rows.z input source.2.2 }

/-- This function applies the actual coordinate mask maps at all circuit positions. -/
def circuitMaskSampleGarble (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) : PublicSample := {
  curve := curveMaskSampleGarble bridgeKey mask input source.1
  points := Vector.ofFn fun index => rowMaskSampleGarble (rows.get index) input (source.2 index) }

private theorem xMaskSampleGarble_split (row : Coordinates.Coefficients)
    (input : AffineInput) (sample : XPublicSample) :
    xMaskSampleGarble row input (xMaskSampleSplit row input sample).2 =
      sample.retargetMask input (xMaskPolynomial row.constant ![row.x, row.y, row.xy, row.ySquared] input) := by
  unfold xMaskSampleGarble xMaskSampleSplit
  rw [maskSampleSplitEquiv_selected]
  exact xSample_pivot sample input _

private theorem yMaskSampleGarble_split (row : Coordinates.Coefficients)
    (input : AffineInput) (sample : YPublicSample) :
    yMaskSampleGarble row input (yMaskSampleSplit row input sample).2 =
      sample.retargetMask input (yMaskPolynomial row.constant ![row.x, row.xSquared, row.ySquared] input) := by
  unfold yMaskSampleGarble yMaskSampleSplit
  rw [maskSampleSplitEquiv_selected]
  exact ySample_pivot sample input _

private theorem zMaskSampleGarble_split (row : Coordinates.Coefficients)
    (input : AffineInput) (sample : ZPublicSample) :
    zMaskSampleGarble row input (zMaskSampleSplit row input sample).2 =
      sample.retargetMask input (zMaskPolynomial row.constant ![row.y, row.xy, row.xSquared, row.ySquared] input) := by
  unfold zMaskSampleGarble zMaskSampleSplit
  rw [maskSampleSplitEquiv_selected]
  exact zSample_pivot sample input _

private theorem curveMaskSampleGarble_split (bridgeKey mask : BaseField)
    (input : AffineInput) (sample : CurvePublicSample) :
    curveMaskSampleGarble bridgeKey mask input (curveMaskSampleSplit bridgeKey mask input sample).2 =
      sample.retargetMask input (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)) := by
  unfold curveMaskSampleGarble curveMaskSampleSplit
  rw [maskSampleSplitEquiv_selected]
  exact curveSample_pivot sample input _

/-- This sample update uses the actual homogeneous row target. -/
def RowPublicSample.retargetMask (sample : RowPublicSample) (input : AffineInput)
    (target : FieldMacToECMac.HomogeneousValue) : RowPublicSample := {
  x := sample.x.retargetMask input target.x
  y := sample.y.retargetMask input target.y
  z := sample.z.retargetMask input target.z }

@[simp] theorem RowPublicSample.retargetMask_request (sample : RowPublicSample)
    (input : AffineInput) (target : FieldMacToECMac.HomogeneousValue) :
    (sample.retargetMask input target).request = sample.request.retarget input target := by
  simp only [retargetMask, RowPublicSample.request, BiquadraticRowRequest.retarget,
    XPublicSample.retargetMask_request, YPublicSample.retargetMask_request,
    ZPublicSample.retargetMask_request]

/-- This update keeps all circuit tables and quotients. -/
def PublicSample.retargetMask (sample : PublicSample) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    PublicSample := {
  curve := sample.curve.retargetMask input curveTarget
  points := Vector.ofFn fun index =>
    (sample.points.get index).retargetMask input (targets.get index) }

@[simp] theorem PublicSample.retargetMask_curveRequest (sample : PublicSample)
    (input : AffineInput) (curveTarget : BaseField)
    (targets : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    (sample.retargetMask input curveTarget targets).curveRequest =
      sample.curveRequest.retarget input curveTarget :=
  sample.curve.retargetMask_request input curveTarget

private theorem vectorMapOfFn {A B : Type} {count : Nat} (values : Fin count → A) (f : A → B) :
    (Vector.ofFn values).map f = Vector.ofFn (fun index => f (values index)) := by
  apply Vector.ext
  intro index inRange
  simp only [Vector.getElem_map, Vector.getElem_ofFn]

@[simp] theorem PublicSample.retargetMask_pointRequests (sample : PublicSample)
    (input : AffineInput) (curveTarget : BaseField)
    (targets : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    (sample.retargetMask input curveTarget targets).pointRequests =
      retargetPointGateRequests sample.pointRequests input targets := by
  unfold PublicSample.pointRequests PublicSample.retargetMask retargetPointGateRequests
  rw [vectorMapOfFn]
  apply congrArg Vector.ofFn
  funext index
  rw [Vector.get_map]
  exact RowPublicSample.retargetMask_request _ _ _

private theorem rowMaskSampleGarble_split (rows : Coordinates.Rows)
    (sparse : FieldMacToECMac.SparseRow rows) (input : AffineInput) (sample : RowPublicSample) :
    rowMaskSampleGarble rows input (rowMaskSampleSplit rows input sample).2 =
      sample.retargetMask input (FieldMacToECMac.evaluateRowCubic rows input) := by
  have hx : xMaskPolynomial rows.x.constant
      ![rows.x.x, rows.x.y, rows.x.xy, rows.x.ySquared] input =
      Coordinates.evaluate rows.x input := by
    simp [xMaskPolynomial, Coordinates.evaluate, sparse.1]
    ring
  have hy : yMaskPolynomial rows.y.constant
      ![rows.y.x, rows.y.xSquared, rows.y.ySquared] input =
      FieldMacToECMac.evaluateCubicY rows.y input := by
    simp [yMaskPolynomial, FieldMacToECMac.evaluateCubicY]
  have hz : zMaskPolynomial rows.z.constant
      ![rows.z.y, rows.z.xy, rows.z.xSquared, rows.z.ySquared] input =
      Coordinates.evaluate rows.z input := by
    simp [zMaskPolynomial, Coordinates.evaluate, sparse.2.2.2]
    ring
  change ({
    x := xMaskSampleGarble rows.x input (xMaskSampleSplit rows.x input sample.x).2,
    y := yMaskSampleGarble rows.y input (yMaskSampleSplit rows.y input sample.y).2,
    z := zMaskSampleGarble rows.z input (zMaskSampleSplit rows.z input sample.z).2 } :
      RowPublicSample) = _
  rw [xMaskSampleGarble_split, yMaskSampleGarble_split, zMaskSampleGarble_split, hx, hy, hz]
  rfl

/-- The circuit equivalence keeps the exact selected result at every gate. -/
theorem circuitMaskSampleGarble_split (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (input : AffineInput) (sample : PublicSample) :
    circuitMaskSampleGarble bridgeKey mask rows input
      (circuitMaskSampleSplit bridgeKey mask rows input sample).2 =
      sample.retargetMask input (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2))
        (FieldMacToECMac.evaluateRowsCubic rows input) := by
  change ({
    curve := curveMaskSampleGarble bridgeKey mask input
      (curveMaskSampleSplit bridgeKey mask input sample.curve).2,
    points := Vector.ofFn fun index => rowMaskSampleGarble (rows.get index) input
      (rowMaskSampleSplit (rows.get index) input (sample.points.get index)).2 } : PublicSample) = _
  rw [curveMaskSampleGarble_split]
  have points : (Vector.ofFn fun index => rowMaskSampleGarble (rows.get index) input
      (rowMaskSampleSplit (rows.get index) input (sample.points.get index)).2) =
      Vector.ofFn (fun index => (sample.points.get index).retargetMask input
        ((FieldMacToECMac.evaluateRowsCubic rows input).get index)) := by
    apply congrArg Vector.ofFn
    funext index
    change rowMaskSampleGarble (rows.get index) input
      (rowMaskSampleSplit (rows.get index) input (sample.points.get index)).2 =
      (sample.points.get index).retargetMask input
        ((Vector.ofFn fun output => FieldMacToECMac.evaluateRowCubic (rows.get output) input).get index)
    rw [Vector.get_ofFn]
    exact rowMaskSampleGarble_split (rows.get index) (sparse index) input _
  rw [points]
  rfl

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩

/-- The independent mask source and the retargeted public sampler have the same full law. -/
theorem circuitMaskGarble_eq_publicSampleRetarget (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (input : AffineInput) :
    (PMF.uniformOfFintype CircuitMaskSample).map (circuitMaskSampleGarble bridgeKey mask rows input) =
      (PMF.uniformOfFintype PublicSample).map (fun sample =>
        sample.retargetMask input (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2))
          (FieldMacToECMac.evaluateRowsCubic rows input)) := by
  let split := circuitMaskSampleSplit bridgeKey mask rows input
  have marginal : (PMF.uniformOfFintype PublicSample).map (fun sample => (split sample).2) =
      PMF.uniformOfFintype CircuitMaskSample := by
    change (PMF.uniformOfFintype PublicSample).map (Prod.snd ∘ split) = _
    rw [← PMF.map_comp, map_uniformOfFintype_equivBetween split, map_uniform_prod_snd]
  rw [← marginal, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype PublicSample).map)
  funext sample
  exact circuitMaskSampleGarble_split bridgeKey mask rows sparse input sample

/-- This function exposes the complete selected programming requests. -/
def PublicSample.requests (sample : PublicSample) : CurveGateRequest × PointGateRequests :=
  (sample.curveRequest, sample.pointRequests)

/-- This law uses the actual simulator requests and all selected hash lifts. -/
theorem circuitMaskGarble_eq_selectedRequests (bridgeKey mask : BaseField)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (input : AffineInput) :
    ((PMF.uniformOfFintype CircuitMaskSample).map
      (circuitMaskSampleGarble bridgeKey mask rows input)).map PublicSample.requests =
    (PMF.uniformOfFintype PublicSample).map (fun sample =>
      (sample.curveRequest.retarget input (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)),
        retargetPointGateRequests sample.pointRequests input
          (FieldMacToECMac.evaluateRowsCubic rows input))) := by
  rw [circuitMaskGarble_eq_publicSampleRetarget bridgeKey mask rows sparse input, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype PublicSample).map)
  funext sample
  exact Prod.ext (PublicSample.retargetMask_curveRequest sample input _ _)
    (PublicSample.retargetMask_pointRequests sample input _ _)

/-- The actual output-key rows satisfy the sparse-row conditions. -/
theorem outputKeyMaskGarble_eq_selectedRequests (bridgeKey mask : BaseField)
    (keys : FieldMacToECMac.OutputKeys) (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (onCurve : OnCurve input) :
    ((PMF.uniformOfFintype CircuitMaskSample).map (circuitMaskSampleGarble bridgeKey mask
      (FieldMacToECMac.rowsForOutputKeys keys randomness) input)).map PublicSample.requests =
    (PMF.uniformOfFintype PublicSample).map (fun sample =>
      (sample.curveRequest.retarget input bridgeKey,
        retargetPointGateRequests sample.pointRequests input
          (FieldMacToECMac.evaluateRows (FieldMacToECMac.rowsForOutputKeys keys randomness) input))) := by
  rw [← FieldMacToECMac.evaluateRowsCubic_eq _
    (FieldMacToECMac.rowsForOutputKeysSparse keys randomness) input onCurve]
  have curveTarget : bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) = bridgeKey := by
    rw [show input.y ^ 2 = input.x ^ 3 + 3 from onCurve]
    simp
  simpa only [curveTarget] using circuitMaskGarble_eq_selectedRequests bridgeKey mask
    (FieldMacToECMac.rowsForOutputKeys keys randomness)
    (FieldMacToECMac.rowsForOutputKeysSparse keys randomness) input

end
end Kriterion.ArgoMAC.Security
