import Proof.Privacy.Distribution.BiquadraticDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- This sample contains two field randomizers and five mask vectors. -/
abbrev CurveMaskData :=
  (Fin 2 → BaseField) × (Fin 5 → Fin coordinateBitCount → BaseField)

/-- This view contains the public coefficients and selected mask vectors. -/
abbrev CurveMaskView :=
  (Fin 3 → BaseField) × (Fin 5 → Fin coordinateBitCount → BaseField)

/-- The selected mask change has a triangular inverse. -/
def curveMaskShiftEquiv (mask : BaseField) (input : AffineInput) :
    CurveMaskData ≃ CurveMaskData where
  toFun data :=
    (![(Equiv.addLeft mask) (data.1 0), (Equiv.addLeft (-mask)) (data.1 1)],
      ![maskShiftEquiv (-(data.1 0)) input.x (data.2 0),
        maskShiftEquiv (-(DigitAdaptor.fromBits (data.2 0))) input.x (data.2 1),
        maskShiftEquiv (-(DigitAdaptor.fromBits (data.2 1))) input.x (data.2 2),
        maskShiftEquiv (-(data.1 1)) input.y (data.2 3),
        maskShiftEquiv (-(DigitAdaptor.fromBits (data.2 3))) input.y (data.2 4)])
  invFun data :=
    let r1 := (Equiv.addLeft mask).symm (data.1 0)
    let r2 := (Equiv.addLeft (-mask)).symm (data.1 1)
    let x3 := (maskShiftEquiv (-r1) input.x).symm (data.2 0)
    let x5 := (maskShiftEquiv (-(DigitAdaptor.fromBits x3)) input.x).symm (data.2 1)
    let x7 := (maskShiftEquiv (-(DigitAdaptor.fromBits x5)) input.x).symm (data.2 2)
    let y4 := (maskShiftEquiv (-r2) input.y).symm (data.2 3)
    let y6 := (maskShiftEquiv (-(DigitAdaptor.fromBits y4)) input.y).symm (data.2 4)
    (![r1, r2], ![x3, x5, x7, y4, y6])
  left_inv data := by
    apply Prod.ext <;> funext index <;> fin_cases index <;> simp
  right_inv data := by
    apply Prod.ext <;> funext index <;> fin_cases index <;> simp

/-- This expression contains every term except the public constant. -/
def curveMaskRest (input : AffineInput) (data : CurveMaskData) : BaseField :=
  data.1 0 * input.x ^ 3 + data.1 1 * input.y ^ 2 +
    DigitAdaptor.fromBits (data.2 0) * input.x ^ 2 +
    DigitAdaptor.fromBits (data.2 3) * input.y +
    DigitAdaptor.fromBits (data.2 1) * input.x +
    DigitAdaptor.fromBits (data.2 4) + DigitAdaptor.fromBits (data.2 2)

/-- This expression is the selected curve result. -/
def curveMaskResult (input : AffineInput) (view : CurveMaskView) : BaseField :=
  view.1 0 + curveMaskRest input ((fun index => view.1 index.succ), view.2)

/-- The result fixes the constant once the other values are known. -/
def curveMaskFiberEquiv (input : AffineInput) (target : BaseField) :
    CurveMaskData ≃ {view : CurveMaskView // curveMaskResult input view = target} :=
  maskViewFiberEquiv (curveMaskRest input) target

/-- The real masks map to the exact curve output fiber. -/
def curveMaskViewEquiv (bridgeKey mask : BaseField) (input : AffineInput) :
    CurveMaskData ≃ {view : CurveMaskView // curveMaskResult input view =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)} :=
  (curveMaskShiftEquiv mask input).trans
    (curveMaskFiberEquiv input (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)))

/-- The first coefficient agrees with the concrete garbler. -/
theorem curveMaskViewEquiv_constant (bridgeKey mask : BaseField) (input : AffineInput)
    (data : CurveMaskData) :
    (curveMaskViewEquiv bridgeKey mask input data).1.1 0 =
      3 * mask + bridgeKey - DigitAdaptor.fromBits (data.2 4) -
        DigitAdaptor.fromBits (data.2 2) := by
  change bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) -
    curveMaskRest input (curveMaskShiftEquiv mask input data) = _
  simp [curveMaskRest, curveMaskShiftEquiv, Equiv.addLeft, fromBits_maskShift]
  ring

/-- The request evaluator uses the curve mask result. -/
theorem CurveGateRequest.result_eq_curveMaskResult (request : CurveGateRequest)
    (input : AffineInput) :
    request.result input = curveMaskResult input
      (![request.c0, request.c1, request.c2],
        ![request.x3Targets, request.x5Targets, request.x7Targets,
          request.y4Targets, request.y6Targets]) := by
  simp [CurveGateRequest.result, curveMaskResult, curveMaskRest]
  ring

/-- Uniform real masks give the uniform distribution on the curve output fiber. -/
theorem map_uniform_curveMaskView (bridgeKey mask : BaseField) (input : AffineInput) :
    letI : Nonempty {view : CurveMaskView // curveMaskResult input view =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)} :=
        ⟨curveMaskViewEquiv bridgeKey mask input (0, 0)⟩
    (PMF.uniformOfFintype CurveMaskData).map (curveMaskViewEquiv bridgeKey mask input) =
      PMF.uniformOfFintype {view : CurveMaskView // curveMaskResult input view =
        bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)} := by
  letI : Nonempty {view : CurveMaskView // curveMaskResult input view =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)} :=
    ⟨curveMaskViewEquiv bridgeKey mask input (0, 0)⟩
  exact map_uniformOfFintype_equivBetween (curveMaskViewEquiv bridgeKey mask input)

/-- These values are the real randomizers and false-label hash masks. -/
def curveMaskSource (r1 r2 : BaseField) (oracles : CurveMembership.Oracles)
    (key : InputMacKey) : CurveMaskData :=
  (![r1, r2],
    ![(fun index => (oracles.x3 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.x5 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.x7 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.y4 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.y6 index.val).hashToField (key.y.get index).falseLabel)])

/-- The mask map contains the actual public curve coefficients. -/
theorem garble_curveMaskCoefficients (bridgeKey mask r1 r2 : BaseField)
    (oracles : CurveMembership.Oracles) (key : InputMacKey) (input : AffineInput) :
    let table := CurveMembership.garble bridgeKey mask r1 r2 oracles key
    ![table.c0, table.c1, table.c2] =
      (curveMaskViewEquiv bridgeKey mask input (curveMaskSource r1 r2 oracles key)).1.1 := by
  funext index
  fin_cases index
  · change (CurveMembership.garble bridgeKey mask r1 r2 oracles key).c0 =
      (curveMaskViewEquiv bridgeKey mask input (curveMaskSource r1 r2 oracles key)).1.1 0
    rw [curveMaskViewEquiv_constant]
    simp [CurveMembership.garble, curveMaskSource,
      DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble]
  · rfl
  · rfl

/-- This pivot changes the low x7 mask in the curve view. -/
def curveMaskPivot (amount : BaseField) (view : CurveMaskView) : CurveMaskView :=
  (view.1, Function.update view.2 2 (lowMaskShift amount (view.2 2)))

theorem curveMaskPivot_zero (view : CurveMaskView) : curveMaskPivot 0 view = view := by
  simp [curveMaskPivot]

theorem curveMaskPivot_add (first second : BaseField) (view : CurveMaskView) :
    curveMaskPivot first (curveMaskPivot second view) = curveMaskPivot (first + second) view := by
  simp [curveMaskPivot, lowMaskShift_add]

theorem curveMaskResult_pivot (input : AffineInput) (amount : BaseField)
    (view : CurveMaskView) :
    curveMaskResult input (curveMaskPivot amount view) = curveMaskResult input view + amount := by
  simp [curveMaskResult, curveMaskRest, curveMaskPivot, fromBits_lowMaskShift]
  ring

/-- The pivot is the actual simulator retarget operation on the mask view. -/
theorem CurveGateRequest.retarget_maskView (request : CurveGateRequest)
    (input : AffineInput) (target : BaseField) :
    curveMaskPivot (target - request.result input)
      (![request.c0, request.c1, request.c2],
        ![request.x3Targets, request.x5Targets, request.x7Targets,
          request.y4Targets, request.y6Targets]) =
      (![(request.retarget input target).c0, (request.retarget input target).c1,
        (request.retarget input target).c2],
        ![(request.retarget input target).x3Targets, (request.retarget input target).x5Targets,
          (request.retarget input target).x7Targets, (request.retarget input target).y4Targets,
          (request.retarget input target).y6Targets]) := by
  apply Prod.ext
  · rfl
  · funext index
    fin_cases index <;>
      simp [curveMaskPivot, CurveGateRequest.retarget, lowMaskShift_eq_retargetBits, add_comm]

/-- The real curve masks and the simulator pivot have the same view distribution. -/
theorem curveMask_real_eq_simulated (bridgeKey mask : BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype CurveMaskData).map
        (fun data => (curveMaskViewEquiv bridgeKey mask input data).1) =
      (PMF.uniformOfFintype CurveMaskView).map (fun view =>
        curveMaskPivot (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) -
          curveMaskResult input view) view) := by
  rw [map_uniform_retargetOfShift (curveMaskResult input) curveMaskPivot
    curveMaskPivot_zero curveMaskPivot_add (curveMaskResult_pivot input)]
  rw [← map_uniform_curveMaskView bridgeKey mask input, PMF.map_comp]
  rfl

/-- The mask map contains the actual selected curve target vectors. -/
theorem garble_curveMaskTargets (bridgeKey mask r1 r2 : BaseField)
    (oracles : CurveMembership.Oracles) (key : InputMacKey) (input : AffineInput) :
    let x3 := DigitAdaptor.garble oracles.x3 (-r1) key.x
    let x5 := DigitAdaptor.garble oracles.x5 (-DigitAdaptor.bitsK x3.2) key.x
    let x7 := DigitAdaptor.garble oracles.x7 (-DigitAdaptor.bitsK x5.2) key.x
    let y4 := DigitAdaptor.garble oracles.y4 (-r2) key.y
    let y6 := DigitAdaptor.garble oracles.y6 (-DigitAdaptor.bitsK y4.2) key.y
    ![(fun index => (DigitAdaptor.selectedOutputs x3.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x5.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x7.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y4.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y6.2 (coordinateValues input.y)).get index)] =
      (curveMaskViewEquiv bridgeKey mask input (curveMaskSource r1 r2 oracles key)).1.2 := by
  dsimp only
  simp only [digitGarble_selectedOutputs_eq, digitGarble_bitsK_eq]
  rfl

/-- This equivalence separates the mask view from the public table rows and hash quotients. -/
def curveSampleViewEquiv : CurvePublicSample ≃ CurveMaskView ×
    ((Fin 5 → Vector BitAdaptor.Table coordinateBitCount) ×
      (Fin 5 → Fin coordinateBitCount → HashLiftQuotient)) where
  toFun sample := ((sample.coefficients, sample.targets), (sample.tables, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    targets := pair.1.2
    tables := pair.2.1
    quotients := pair.2.2
  }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual curve simulator samples a uniform mask view. -/
theorem map_uniform_curveSampleView :
    letI : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
    (PMF.uniformOfFintype CurvePublicSample).map
        (fun sample => (sample.coefficients, sample.targets)) =
      PMF.uniformOfFintype CurveMaskView := by
  letI : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
  letI : Fintype BitAdaptor.Table := bitAdaptorTableFintype
  letI : Fintype (Vector BitAdaptor.Table coordinateBitCount) := publicVectorFintype
  letI : Nonempty BitAdaptor.Table := ⟨defaultBitAdaptorTable⟩
  letI : Nonempty (Vector BitAdaptor.Table coordinateBitCount) :=
    ⟨Vector.replicate coordinateBitCount defaultBitAdaptorTable⟩
  change (PMF.uniformOfFintype CurvePublicSample).map (Prod.fst ∘ curveSampleViewEquiv) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween curveSampleViewEquiv,
    map_uniform_prod_fst]

end

end Kriterion.ArgoMAC.Security
