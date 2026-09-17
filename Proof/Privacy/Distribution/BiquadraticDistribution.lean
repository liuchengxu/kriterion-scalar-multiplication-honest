import Proof.Privacy.Distribution.AlgebraicDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- This shape stores four coefficients and four complete mask vectors. -/
abbrev XMaskData :=
  (Fin 4 → BaseField) × (Fin 4 → Fin coordinateBitCount → BaseField)

/-- This shape stores the public coefficients and selected mask vectors. -/
abbrev XMaskView :=
  (Fin 5 → BaseField) × (Fin 4 → Fin coordinateBitCount → BaseField)

/-- These values are the randomizers and actual false-branch hash offsets. -/
def xMaskSource (randomness : Biquadratic.XRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey) : XMaskData :=
  (![randomness.r1, randomness.r2, randomness.r3, randomness.r5],
    ![(fun index => (oracles.y6 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.y8 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.y10 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.x9 index.val).hashToField (key.x.get index).falseLabel)])

/-- These coefficients use the actual X-coordinate mask equations. -/
def xMaskPublicCoefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (source : XMaskData) : Fin 5 → BaseField :=
  Fin.cases (c0 - DigitAdaptor.fromBits (source.2 2) -
    DigitAdaptor.fromBits (source.2 3)) (fun index => coefficients index + source.1 index)

/-- The concrete garbler publishes the coefficients in the mask map. -/
theorem garbleX_maskCoefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles)
    (key : InputMacKey) :
    let table := Biquadratic.garbleX c0 (coefficients 0) (coefficients 1)
      (coefficients 2) (coefficients 3) randomness oracles key
    ![table.c0.getD 0, table.c1.getD 0, table.c2.getD 0, table.c3.getD 0,
      table.c5.getD 0] =
      xMaskPublicCoefficients c0 coefficients (xMaskSource randomness oracles key) := by
  funext index
  fin_cases index <;>
    simp [Biquadratic.garbleX, xMaskPublicCoefficients, xMaskSource,
      DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble] <;> rfl

/-- The bit-adaptor offsets are exactly its false-branch hash values. -/
theorem digitGarble_bitsK_eq {count : Nat} (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (keys : Vector BitAdaptor.Key count) :
    DigitAdaptor.bitsK (DigitAdaptor.garble windows slope keys).2 =
      DigitAdaptor.fromBits (fun index =>
        (windows index.val).hashToField (keys.get index).falseLabel) := by
  simp [DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble]

/-- The selected outputs apply the shared mask shift to those hash offsets. -/
theorem digitGarble_selectedOutputs_eq (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope input : BaseField) (keys : CoordinateMacKey) :
    (fun index => (DigitAdaptor.selectedOutputs
      (DigitAdaptor.garble windows slope keys).2 (coordinateValues input)).get index) =
      maskShiftEquiv slope input (fun index =>
        (windows index.val).hashToField (keys.get index).falseLabel) := by
  funext index
  simp [DigitAdaptor.selectedOutputs, DigitAdaptor.garble, BitAdaptor.garble,
    BitAdaptor.OutputKey.encode, maskShiftEquiv]

/-- The triangular mask map recovers every source value from selected targets. -/
def xMaskSelectedEquiv (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    XMaskData ≃ XMaskData where
  toFun source :=
    ((fun index => coefficients index + source.1 index),
      ![maskShiftEquiv (-source.1 2) input.y (source.2 0),
        maskShiftEquiv (-source.1 3) input.y (source.2 1),
        maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 1))) input.y
          (source.2 2),
        maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 0))) input.x
          (source.2 3)])
  invFun selected :=
    let r := fun index => selected.1 index - coefficients index
    let y6 := (maskShiftEquiv (-r 2) input.y).symm (selected.2 0)
    let y8 := (maskShiftEquiv (-r 3) input.y).symm (selected.2 1)
    (r, ![y6, y8,
      (maskShiftEquiv (-(r 1 + DigitAdaptor.fromBits y8)) input.y).symm (selected.2 2),
      (maskShiftEquiv (-(r 0 + DigitAdaptor.fromBits y6)) input.x).symm (selected.2 3)])
  left_inv source := by
    apply Prod.ext
    · funext index
      simp
    · funext index
      fin_cases index <;> simp
  right_inv selected := by
    apply Prod.ext
    · funext index
      simp
    · funext index
      fin_cases index <;> simp

/-- This expression omits only the public constant coefficient. -/
def xMaskRest (input : AffineInput) (data : XMaskData) : BaseField :=
  data.1 0 * input.x + data.1 1 * input.y + data.1 2 * input.x * input.y +
    data.1 3 * input.y ^ 2 + DigitAdaptor.fromBits (data.2 0) * input.x +
    DigitAdaptor.fromBits (data.2 1) * input.y +
    DigitAdaptor.fromBits (data.2 3) + DigitAdaptor.fromBits (data.2 2)

/-- This expression is the selected X-coordinate polynomial view. -/
def xMaskResult (input : AffineInput) (view : XMaskView) : BaseField :=
  view.1 0 + xMaskRest input ((fun index => view.1 index.succ), view.2)

/-- This projection keeps the request's public coefficients and selected targets. -/
def BiquadraticXRequest.maskView (request : BiquadraticXRequest) : XMaskView :=
  (![request.c0, request.c1, request.c2, request.c3, request.c5],
    ![request.y6Targets, request.y8Targets, request.y10Targets, request.x9Targets])

/-- The request evaluator uses the same polynomial view. -/
theorem BiquadraticXRequest.result_eq_xMaskResult (request : BiquadraticXRequest)
    (input : AffineInput) :
    request.result input = xMaskResult input request.maskView := by
  simp [BiquadraticXRequest.result, BiquadraticXRequest.maskView, xMaskResult, xMaskRest]
  ring

/-- The output fixes the constant coefficient once all other values are known. -/
def maskViewFiberEquiv {count : Nat} {Masks : Type*}
    (rest : (Fin count → BaseField) × Masks → BaseField) (target : BaseField) :
    ((Fin count → BaseField) × Masks) ≃
      {view : (Fin (count + 1) → BaseField) × Masks //
        view.1 0 + rest ((fun index => view.1 index.succ), view.2) = target} where
  toFun data := ⟨(Fin.cases (target - rest data) data.1, data.2), by simp⟩
  invFun view := ((fun index => view.1.1 index.succ), view.1.2)
  left_inv _ := rfl
  right_inv view := by
    apply Subtype.ext
    apply Prod.ext
    · funext index
      refine Fin.cases ?_ (fun _ => rfl) index
      change target - rest ((fun index => view.1.1 index.succ), view.1.2) = view.1.1 0
      exact sub_eq_iff_eq_add.mpr view.2.symm
    · rfl

/-- This specialization fixes the X-coordinate polynomial result. -/
def xMaskFiberEquiv (input : AffineInput) (target : BaseField) :
    XMaskData ≃ {view : XMaskView // xMaskResult input view = target} :=
  maskViewFiberEquiv (xMaskRest input) target

/-- This value is the polynomial that the concrete X garbler evaluates. -/
def xMaskPolynomial (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) : BaseField :=
  c0 + coefficients 0 * input.x + coefficients 1 * input.y +
    coefficients 2 * input.x * input.y + coefficients 3 * input.y ^ 2

/-- This equivalence gives the complete X mask change of variables. -/
def xMaskGarbleEquiv (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) :
    XMaskData ≃ {view : XMaskView //
      xMaskResult input view = xMaskPolynomial c0 coefficients input} :=
  (xMaskSelectedEquiv coefficients input).trans
    (xMaskFiberEquiv input (xMaskPolynomial c0 coefficients input))

/-- The change of variables gives every coefficient that garbleX publishes. -/
theorem xMaskGarbleEquiv_coefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (source : XMaskData) :
    (xMaskGarbleEquiv c0 coefficients input source).1.1 =
      xMaskPublicCoefficients c0 coefficients source := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  change xMaskPolynomial c0 coefficients input -
    ((coefficients 0 + source.1 0) * input.x +
      (coefficients 1 + source.1 1) * input.y +
      (coefficients 2 + source.1 2) * input.x * input.y +
      (coefficients 3 + source.1 3) * input.y ^ 2 +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 2) input.y (source.2 0)) * input.x +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 3) input.y (source.2 1)) * input.y +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 0)))
        input.x (source.2 3)) +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 1)))
        input.y (source.2 2))) =
    c0 - DigitAdaptor.fromBits (source.2 2) - DigitAdaptor.fromBits (source.2 3)
  rw [fromBits_maskShift, fromBits_maskShift, fromBits_maskShift, fromBits_maskShift]
  unfold xMaskPolynomial
  ring

/-- The concrete adaptors produce the selected targets in the change of variables. -/
theorem garbleX_maskTargets (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles)
    (key : InputMacKey) (input : AffineInput) :
    let y6 := DigitAdaptor.garble oracles.y6 (-randomness.r3) key.y
    let y8 := DigitAdaptor.garble oracles.y8 (-randomness.r5) key.y
    let y10 := DigitAdaptor.garble oracles.y10
      (-(randomness.r2 + DigitAdaptor.bitsK y8.2)) key.y
    let x9 := DigitAdaptor.garble oracles.x9
      (-(randomness.r1 + DigitAdaptor.bitsK y6.2)) key.x
    ![(fun index => (DigitAdaptor.selectedOutputs y6.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y8.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y10.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x9.2 (coordinateValues input.x)).get index)] =
      (xMaskGarbleEquiv c0 coefficients input (xMaskSource randomness oracles key)).1.2 := by
  dsimp only
  simp only [digitGarble_selectedOutputs_eq, digitGarble_bitsK_eq]
  rfl

/-- Uniform real masks give the uniform X polynomial fiber. -/
theorem map_uniform_xMaskGarbleEquiv (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) :
    letI : Nonempty {view : XMaskView //
      xMaskResult input view = xMaskPolynomial c0 coefficients input} :=
        ⟨xMaskGarbleEquiv c0 coefficients input (0, 0)⟩
    (PMF.uniformOfFintype XMaskData).map (xMaskGarbleEquiv c0 coefficients input) =
      PMF.uniformOfFintype {view : XMaskView //
        xMaskResult input view = xMaskPolynomial c0 coefficients input} := by
  letI : Nonempty {view : XMaskView //
      xMaskResult input view = xMaskPolynomial c0 coefficients input} :=
    ⟨xMaskGarbleEquiv c0 coefficients input (0, 0)⟩
  exact map_uniformOfFintype_equivBetween (xMaskGarbleEquiv c0 coefficients input)

/-- An additive pivot separates the result from a fixed result fiber. -/
def resultFiberSplitEquiv {View : Type*} (result : View → BaseField)
    (shift : BaseField → View → View)
    (shiftZero : ∀ view, shift 0 view = view)
    (shiftAdd : ∀ first second view, shift first (shift second view) = shift (first + second) view)
    (resultShift : ∀ amount view, result (shift amount view) = result view + amount)
    (target : BaseField) : View ≃ BaseField × {view // result view = target} where
  toFun view := (result view, ⟨shift (target - result view) view, by rw [resultShift]; ring⟩)
  invFun pair := shift (pair.1 - target) pair.2.1
  left_inv view := by
    change shift (result view - target) (shift (target - result view) view) = view
    rw [shiftAdd]
    have cancel : result view - target + (target - result view) = 0 := by ring
    rw [cancel, shiftZero]
  right_inv pair := by
    apply Prod.ext
    · change result (shift (pair.1 - target) pair.2.1) = pair.1
      rw [resultShift, pair.2.2]
      ring
    · apply Subtype.ext
      change shift (target - result (shift (pair.1 - target) pair.2.1))
        (shift (pair.1 - target) pair.2.1) = pair.2.1
      rw [resultShift, pair.2.2, shiftAdd]
      have cancel : target - (target + (pair.1 - target)) + (pair.1 - target) = 0 := by ring
      rw [cancel, shiftZero]

/-- Retargeting an additive pivot gives the uniform distribution on its result fiber. -/
theorem map_uniform_retargetOfShift {View : Type*} [Fintype View] [Nonempty View]
    (result : View → BaseField) (shift : BaseField → View → View)
    (shiftZero : ∀ view, shift 0 view = view)
    (shiftAdd : ∀ first second view, shift first (shift second view) = shift (first + second) view)
    (resultShift : ∀ amount view, result (shift amount view) = result view + amount)
    (target : BaseField) :
    letI : Nonempty {view // result view = target} :=
      ⟨(resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target
        (Classical.arbitrary View)).2⟩
    (PMF.uniformOfFintype View).map (fun view => shift (target - result view) view) =
      (PMF.uniformOfFintype {view // result view = target}).map Subtype.val := by
  classical
  let e := resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target
  letI : Nonempty {view // result view = target} := ⟨(e (Classical.arbitrary View)).2⟩
  calc
    _ = ((PMF.uniformOfFintype View).map e).map (Subtype.val ∘ Prod.snd) := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (BaseField × {view // result view = target})).map
        (Subtype.val ∘ Prod.snd) := by
      rw [map_uniformOfFintype_equivBetween e]
    _ = _ := by rw [← PMF.map_comp, map_uniform_prod_snd]

/-- This shift adds to the low mask and keeps all other masks. -/
def lowMaskShift {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) : Fin (count + 1) → BaseField :=
  Fin.cases (values 0 + amount) (fun index => values index.succ)

@[simp] theorem lowMaskShift_zero {count : Nat} (values : Fin (count + 1) → BaseField) :
    lowMaskShift 0 values = values := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp [lowMaskShift]

theorem lowMaskShift_add {count : Nat} (first second : BaseField)
    (values : Fin (count + 1) → BaseField) :
    lowMaskShift first (lowMaskShift second values) = lowMaskShift (first + second) values := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp only [lowMaskShift, Fin.cases_zero]
  ring

/-- The low-mask shift adds the same amount to the field total. -/
theorem fromBits_lowMaskShift {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) :
    DigitAdaptor.fromBits (lowMaskShift amount values) = DigitAdaptor.fromBits values + amount := by
  simp only [DigitAdaptor.fromBits, Fin.foldr_succ, lowMaskShift, Fin.cases_zero, Fin.cases_succ]
  ring

/-- The low-mask shift is the simulator's retarget operation. -/
theorem lowMaskShift_eq_retargetBits {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) :
    lowMaskShift amount values = retargetBits values (DigitAdaptor.fromBits values + amount) := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp only [lowMaskShift, retargetBits, Fin.cases_zero, DigitAdaptor.fromBits, Fin.foldr_succ]
  ring

/-- The X pivot changes only the low x9 target. -/
def xMaskPivotShift (amount : BaseField) (view : XMaskView) : XMaskView :=
  (view.1, Function.update view.2 3 (lowMaskShift amount (view.2 3)))

@[simp] theorem xMaskPivotShift_zero (view : XMaskView) : xMaskPivotShift 0 view = view := by
  simp [xMaskPivotShift]

theorem xMaskPivotShift_add (first second : BaseField) (view : XMaskView) :
    xMaskPivotShift first (xMaskPivotShift second view) =
      xMaskPivotShift (first + second) view := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases pivot : index = 3
    · subst index
      simp [xMaskPivotShift, lowMaskShift_add]
    · simp [xMaskPivotShift, pivot]

/-- The pivot adds its amount to the X result. -/
theorem xMaskResult_pivotShift (input : AffineInput) (amount : BaseField) (view : XMaskView) :
    xMaskResult input (xMaskPivotShift amount view) = xMaskResult input view + amount := by
  change view.1 0 +
    (view.1 1 * input.x + view.1 2 * input.y + view.1 3 * input.x * input.y +
      view.1 4 * input.y ^ 2 + DigitAdaptor.fromBits (view.2 0) * input.x +
      DigitAdaptor.fromBits (view.2 1) * input.y +
      DigitAdaptor.fromBits (lowMaskShift amount (view.2 3)) +
      DigitAdaptor.fromBits (view.2 2)) = _
  rw [fromBits_lowMaskShift]
  change _ = view.1 0 +
    (view.1 1 * input.x + view.1 2 * input.y + view.1 3 * input.x * input.y +
      view.1 4 * input.y ^ 2 + DigitAdaptor.fromBits (view.2 0) * input.x +
      DigitAdaptor.fromBits (view.2 1) * input.y +
      DigitAdaptor.fromBits (view.2 3) + DigitAdaptor.fromBits (view.2 2)) + amount
  ring

/-- The request's retarget operation uses this exact low x9 pivot. -/
theorem BiquadraticXRequest.retarget_maskView (request : BiquadraticXRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).maskView =
      xMaskPivotShift (target - xMaskResult input request.maskView) request.maskView := by
  apply Prod.ext
  · rfl
  · funext index
    fin_cases index
    · rfl
    · rfl
    · rfl
    · change retargetBits request.x9Targets
        (target - request.result input + DigitAdaptor.fromBits request.x9Targets) =
          lowMaskShift (target - xMaskResult input request.maskView) request.x9Targets
      rw [lowMaskShift_eq_retargetBits, ← request.result_eq_xMaskResult input]
      apply congrArg (retargetBits request.x9Targets)
      ring

/-- Uniform simulator masks give the uniform X result fiber after retargeting. -/
theorem map_uniform_xMaskRetarget (input : AffineInput) (target : BaseField) :
    letI : Nonempty {view : XMaskView // xMaskResult input view = target} :=
      ⟨xMaskFiberEquiv input target (0, 0)⟩
    (PMF.uniformOfFintype XMaskView).map
      (fun view => xMaskPivotShift (target - xMaskResult input view) view) =
        (PMF.uniformOfFintype {view : XMaskView // xMaskResult input view = target}).map
          Subtype.val := by
  letI : Nonempty {view : XMaskView // xMaskResult input view = target} :=
    ⟨xMaskFiberEquiv input target (0, 0)⟩
  exact map_uniform_retargetOfShift (xMaskResult input) xMaskPivotShift
    xMaskPivotShift_zero xMaskPivotShift_add (xMaskResult_pivotShift input) target

/-- Real X masks and the retargeted simulator have the same complete polynomial view. -/
theorem xMaskGarble_eq_retargetDistribution (c0 : BaseField)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype XMaskData).map
      (fun source => (xMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype XMaskView).map (fun view =>
      xMaskPivotShift (xMaskPolynomial c0 coefficients input - xMaskResult input view) view) := by
  letI : Nonempty {view : XMaskView //
      xMaskResult input view = xMaskPolynomial c0 coefficients input} :=
    ⟨xMaskGarbleEquiv c0 coefficients input (0, 0)⟩
  rw [map_uniform_xMaskRetarget, ← map_uniform_xMaskGarbleEquiv, PMF.map_comp]
  rfl

abbrev YMaskData := (Fin 3 → BaseField) × (Fin 3 → Fin coordinateBitCount → BaseField)
abbrev YMaskView := (Fin 4 → BaseField) × (Fin 3 → Fin coordinateBitCount → BaseField)

/-- These values are the Y randomizers and actual false-branch hash offsets. -/
def yMaskSource (randomness : Biquadratic.YRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey) : YMaskData :=
  (![randomness.r1, randomness.r4, randomness.r5],
    ![(fun index => (oracles.y6 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.x7 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.x9 index.val).hashToField (key.x.get index).falseLabel)])

def yMaskPublicCoefficients (c0 : BaseField) (coefficients : Fin 3 → BaseField)
    (source : YMaskData) : Fin 4 → BaseField :=
  Fin.cases (c0 + 3 * coefficients 2 - DigitAdaptor.fromBits (source.2 2))
    (fun index => coefficients index + source.1 index)

/-- The concrete Y garbler publishes the coefficients in this mask map. -/
theorem garbleY_maskCoefficients (c0 : BaseField) (coefficients : Fin 3 → BaseField)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    let table := Biquadratic.garbleY c0 (coefficients 0) (coefficients 1)
      (coefficients 2) randomness oracles key
    ![table.c0.getD 0, table.c1.getD 0, table.c4.getD 0, table.c5.getD 0] =
      yMaskPublicCoefficients c0 coefficients (yMaskSource randomness oracles key) := by
  funext index
  fin_cases index <;> simp [Biquadratic.garbleY, yMaskPublicCoefficients, yMaskSource,
    DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble] <;> rfl

/-- The inverse recovers y6 before x7 and x7 before x9. -/
def yMaskSelectedEquiv (coefficients : Fin 3 → BaseField) (input : AffineInput) :
    YMaskData ≃ YMaskData where
  toFun source := ((fun index => coefficients index + source.1 index),
    ![maskShiftEquiv (-source.1 2) input.x (source.2 0),
      maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 0))) input.x (source.2 1),
      maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1))) input.x (source.2 2)])
  invFun selected :=
    let r := fun index => selected.1 index - coefficients index
    let y6 := (maskShiftEquiv (-r 2) input.x).symm (selected.2 0)
    let x7 := (maskShiftEquiv (-(r 1 + DigitAdaptor.fromBits y6)) input.x).symm (selected.2 1)
    (r, ![y6, x7,
      (maskShiftEquiv (-(r 0 + DigitAdaptor.fromBits x7)) input.x).symm (selected.2 2)])
  left_inv source := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp
  right_inv selected := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp

def yMaskRest (input : AffineInput) (data : YMaskData) : BaseField :=
  data.1 0 * input.x + data.1 1 * input.x ^ 2 + data.1 2 * input.x ^ 3 +
    DigitAdaptor.fromBits (data.2 0) * input.x ^ 2 +
    DigitAdaptor.fromBits (data.2 1) * input.x +
    DigitAdaptor.fromBits (data.2 2)

def yMaskResult (input : AffineInput) (view : YMaskView) : BaseField :=
  view.1 0 + yMaskRest input ((fun index => view.1 index.succ), view.2)

/-- This is the Y polynomial in the x-only cubic basis. Its constant absorbs the
`3 * c5` residual of rebinding `y ^ 2` to `x ^ 3 + 3`. -/
def yMaskPolynomial (c0 : BaseField) (coefficients : Fin 3 → BaseField)
    (input : AffineInput) : BaseField :=
  c0 + 3 * coefficients 2 + coefficients 0 * input.x + coefficients 1 * input.x ^ 2 +
    coefficients 2 * input.x ^ 3

def BiquadraticYRequest.maskView (request : BiquadraticYRequest) : YMaskView :=
  (![request.c0, request.c1, request.c4, request.c5],
    ![request.y6Targets, request.x7Targets, request.x9Targets])

theorem BiquadraticYRequest.result_eq_yMaskResult (request : BiquadraticYRequest)
    (input : AffineInput) : request.result input = yMaskResult input request.maskView := by
  simp [BiquadraticYRequest.result, BiquadraticYRequest.maskView, yMaskResult, yMaskRest]
  ring

/-- This equivalence gives the complete Y mask change of variables. -/
def yMaskGarbleEquiv (c0 : BaseField) (coefficients : Fin 3 → BaseField) (input : AffineInput) :
    YMaskData ≃ {view : YMaskView // yMaskResult input view = yMaskPolynomial c0 coefficients input} :=
  (yMaskSelectedEquiv coefficients input).trans
    (maskViewFiberEquiv (yMaskRest input) (yMaskPolynomial c0 coefficients input))

theorem yMaskGarbleEquiv_coefficients (c0 : BaseField) (coefficients : Fin 3 → BaseField)
    (input : AffineInput) (source : YMaskData) :
    (yMaskGarbleEquiv c0 coefficients input source).1.1 =
      yMaskPublicCoefficients c0 coefficients source := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  change yMaskPolynomial c0 coefficients input -
    ((coefficients 0 + source.1 0) * input.x + (coefficients 1 + source.1 1) * input.x ^ 2 +
      (coefficients 2 + source.1 2) * input.x ^ 3 +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 2) input.x (source.2 0)) * input.x ^ 2 +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 0)))
        input.x (source.2 1)) * input.x +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1)))
        input.x (source.2 2))) =
    c0 + 3 * coefficients 2 - DigitAdaptor.fromBits (source.2 2)
  rw [fromBits_maskShift, fromBits_maskShift, fromBits_maskShift]
  unfold yMaskPolynomial
  ring

theorem garbleY_maskTargets (c0 : BaseField) (coefficients : Fin 3 → BaseField)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles)
    (key : InputMacKey) (input : AffineInput) :
    let y6 := DigitAdaptor.garble oracles.y6 (-randomness.r5) key.x
    let x7 := DigitAdaptor.garble oracles.x7
      (-(randomness.r4 + DigitAdaptor.bitsK y6.2)) key.x
    let x9 := DigitAdaptor.garble oracles.x9
      (-(randomness.r1 + DigitAdaptor.bitsK x7.2)) key.x
    ![(fun index => (DigitAdaptor.selectedOutputs y6.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x7.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x9.2 (coordinateValues input.x)).get index)] =
      (yMaskGarbleEquiv c0 coefficients input (yMaskSource randomness oracles key)).1.2 := by
  dsimp only
  simp only [digitGarble_selectedOutputs_eq, digitGarble_bitsK_eq]
  rfl

def yMaskPivotShift (amount : BaseField) (view : YMaskView) : YMaskView :=
  (view.1, Function.update view.2 2 (lowMaskShift amount (view.2 2)))

@[simp] theorem yMaskPivotShift_zero (view : YMaskView) : yMaskPivotShift 0 view = view := by
  simp [yMaskPivotShift]

theorem yMaskPivotShift_add (first second : BaseField) (view : YMaskView) :
    yMaskPivotShift first (yMaskPivotShift second view) = yMaskPivotShift (first + second) view := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases pivot : index = 2
    · subst index; simp [yMaskPivotShift, lowMaskShift_add]
    · simp [yMaskPivotShift, pivot]

theorem yMaskResult_pivotShift (input : AffineInput) (amount : BaseField) (view : YMaskView) :
    yMaskResult input (yMaskPivotShift amount view) = yMaskResult input view + amount := by
  change view.1 0 + (view.1 1 * input.x + view.1 2 * input.x ^ 2 + view.1 3 * input.x ^ 3 +
    DigitAdaptor.fromBits (view.2 0) * input.x ^ 2 +
    DigitAdaptor.fromBits (view.2 1) * input.x +
    DigitAdaptor.fromBits (lowMaskShift amount (view.2 2))) =
    view.1 0 + (view.1 1 * input.x + view.1 2 * input.x ^ 2 + view.1 3 * input.x ^ 3 +
    DigitAdaptor.fromBits (view.2 0) * input.x ^ 2 +
    DigitAdaptor.fromBits (view.2 1) * input.x +
    DigitAdaptor.fromBits (view.2 2)) + amount
  rw [fromBits_lowMaskShift]
  ring

theorem BiquadraticYRequest.retarget_maskView (request : BiquadraticYRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).maskView =
      yMaskPivotShift (target - yMaskResult input request.maskView) request.maskView := by
  apply Prod.ext
  · rfl
  · funext index
    fin_cases index
    · rfl
    · rfl
    · change retargetBits request.x9Targets
        (target - request.result input + DigitAdaptor.fromBits request.x9Targets) =
          lowMaskShift (target - yMaskResult input request.maskView) request.x9Targets
      rw [lowMaskShift_eq_retargetBits, ← request.result_eq_yMaskResult input]
      apply congrArg (retargetBits request.x9Targets)
      ring

/-- Real Y masks and the corrected simulator give the same complete polynomial view. -/
theorem yMaskGarble_eq_retargetDistribution (c0 : BaseField)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype YMaskData).map
      (fun source => (yMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype YMaskView).map (fun view =>
      yMaskPivotShift (yMaskPolynomial c0 coefficients input - yMaskResult input view) view) := by
  let e := yMaskGarbleEquiv c0 coefficients input
  letI : Nonempty {view : YMaskView //
      yMaskResult input view = yMaskPolynomial c0 coefficients input} := ⟨e (0, 0)⟩
  rw [map_uniform_retargetOfShift (yMaskResult input) yMaskPivotShift
    yMaskPivotShift_zero yMaskPivotShift_add (yMaskResult_pivotShift input),
    ← map_uniformOfFintype_equivBetween e, PMF.map_comp]
  rfl

abbrev ZMaskData := (Fin 4 → BaseField) × (Fin 5 → Fin coordinateBitCount → BaseField)
abbrev ZMaskView := (Fin 5 → BaseField) × (Fin 5 → Fin coordinateBitCount → BaseField)

/-- These values are the Z randomizers and actual false-branch hash offsets. -/
def zMaskSource (randomness : Biquadratic.ZRandomness)
    (oracles : Biquadratic.Oracles) (key : InputMacKey) : ZMaskData :=
  (![randomness.r2, randomness.r3, randomness.r4, randomness.r5],
    ![(fun index => (oracles.y6 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.y8 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.y10 index.val).hashToField (key.y.get index).falseLabel),
      (fun index => (oracles.x7 index.val).hashToField (key.x.get index).falseLabel),
      (fun index => (oracles.x9 index.val).hashToField (key.x.get index).falseLabel)])

def zMaskPublicCoefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (source : ZMaskData) : Fin 5 → BaseField :=
  Fin.cases (c0 - DigitAdaptor.fromBits (source.2 2) - DigitAdaptor.fromBits (source.2 4))
    (fun index => coefficients index + source.1 index)

theorem garbleZ_maskCoefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    let table := Biquadratic.garbleZ c0 (coefficients 0) (coefficients 1)
      (coefficients 2) (coefficients 3) randomness oracles key
    ![table.c0.getD 0, table.c2.getD 0, table.c3.getD 0, table.c4.getD 0, table.c5.getD 0] =
      zMaskPublicCoefficients c0 coefficients (zMaskSource randomness oracles key) := by
  funext index
  fin_cases index <;> simp [Biquadratic.garbleZ, zMaskPublicCoefficients, zMaskSource,
    DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble] <;> rfl

/-- The inverse recovers the three direct masks before the two dependent masks. -/
def zMaskSelectedEquiv (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    ZMaskData ≃ ZMaskData where
  toFun source := ((fun index => coefficients index + source.1 index),
    ![maskShiftEquiv (-source.1 1) input.y (source.2 0),
      maskShiftEquiv (-source.1 3) input.y (source.2 1),
      maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1))) input.y (source.2 2),
      maskShiftEquiv (-source.1 2) input.x (source.2 3),
      maskShiftEquiv (-(DigitAdaptor.fromBits (source.2 0) + DigitAdaptor.fromBits (source.2 3)))
        input.x (source.2 4)])
  invFun selected :=
    let r := fun index => selected.1 index - coefficients index
    let y6 := (maskShiftEquiv (-r 1) input.y).symm (selected.2 0)
    let y8 := (maskShiftEquiv (-r 3) input.y).symm (selected.2 1)
    let x7 := (maskShiftEquiv (-r 2) input.x).symm (selected.2 3)
    (r, ![y6, y8,
      (maskShiftEquiv (-(r 0 + DigitAdaptor.fromBits y8)) input.y).symm (selected.2 2), x7,
      (maskShiftEquiv (-(DigitAdaptor.fromBits y6 + DigitAdaptor.fromBits x7)) input.x).symm
        (selected.2 4)])
  left_inv source := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp
  right_inv selected := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp

def zMaskRest (input : AffineInput) (data : ZMaskData) : BaseField :=
  data.1 0 * input.y + data.1 1 * input.x * input.y + data.1 2 * input.x ^ 2 +
    data.1 3 * input.y ^ 2 + DigitAdaptor.fromBits (data.2 0) * input.x +
    DigitAdaptor.fromBits (data.2 3) * input.x + DigitAdaptor.fromBits (data.2 1) * input.y +
    DigitAdaptor.fromBits (data.2 4) + DigitAdaptor.fromBits (data.2 2)

def zMaskResult (input : AffineInput) (view : ZMaskView) : BaseField :=
  view.1 0 + zMaskRest input ((fun index => view.1 index.succ), view.2)

def zMaskPolynomial (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) : BaseField :=
  c0 + coefficients 0 * input.y + coefficients 1 * input.x * input.y +
    coefficients 2 * input.x ^ 2 + coefficients 3 * input.y ^ 2

def BiquadraticZRequest.maskView (request : BiquadraticZRequest) : ZMaskView :=
  (![request.c0, request.c2, request.c3, request.c4, request.c5],
    ![request.y6Targets, request.y8Targets, request.y10Targets, request.x7Targets, request.x9Targets])

theorem BiquadraticZRequest.result_eq_zMaskResult (request : BiquadraticZRequest)
    (input : AffineInput) : request.result input = zMaskResult input request.maskView := by
  simp [BiquadraticZRequest.result, BiquadraticZRequest.maskView, zMaskResult, zMaskRest]
  ring

/-- This equivalence gives the complete Z mask change of variables. -/
def zMaskGarbleEquiv (c0 : BaseField) (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    ZMaskData ≃ {view : ZMaskView // zMaskResult input view = zMaskPolynomial c0 coefficients input} :=
  (zMaskSelectedEquiv coefficients input).trans
    (maskViewFiberEquiv (zMaskRest input) (zMaskPolynomial c0 coefficients input))

theorem zMaskGarbleEquiv_coefficients (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (input : AffineInput) (source : ZMaskData) :
    (zMaskGarbleEquiv c0 coefficients input source).1.1 =
      zMaskPublicCoefficients c0 coefficients source := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  change zMaskPolynomial c0 coefficients input -
    ((coefficients 0 + source.1 0) * input.y +
      (coefficients 1 + source.1 1) * input.x * input.y +
      (coefficients 2 + source.1 2) * input.x ^ 2 + (coefficients 3 + source.1 3) * input.y ^ 2 +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 1) input.y (source.2 0)) * input.x +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 2) input.x (source.2 3)) * input.x +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 3) input.y (source.2 1)) * input.y +
      DigitAdaptor.fromBits (maskShiftEquiv (-(DigitAdaptor.fromBits (source.2 0) +
        DigitAdaptor.fromBits (source.2 3))) input.x (source.2 4)) +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1)))
        input.y (source.2 2))) =
    c0 - DigitAdaptor.fromBits (source.2 2) - DigitAdaptor.fromBits (source.2 4)
  rw [fromBits_maskShift, fromBits_maskShift, fromBits_maskShift, fromBits_maskShift,
    fromBits_maskShift]
  unfold zMaskPolynomial
  ring

theorem garbleZ_maskTargets (c0 : BaseField) (coefficients : Fin 4 → BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles)
    (key : InputMacKey) (input : AffineInput) :
    let y6 := DigitAdaptor.garble oracles.y6 (-randomness.r3) key.y
    let y8 := DigitAdaptor.garble oracles.y8 (-randomness.r5) key.y
    let y10 := DigitAdaptor.garble oracles.y10
      (-(randomness.r2 + DigitAdaptor.bitsK y8.2)) key.y
    let x7 := DigitAdaptor.garble oracles.x7 (-randomness.r4) key.x
    let x9 := DigitAdaptor.garble oracles.x9
      (-(DigitAdaptor.bitsK y6.2 + DigitAdaptor.bitsK x7.2)) key.x
    ![(fun index => (DigitAdaptor.selectedOutputs y6.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y8.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs y10.2 (coordinateValues input.y)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x7.2 (coordinateValues input.x)).get index),
      (fun index => (DigitAdaptor.selectedOutputs x9.2 (coordinateValues input.x)).get index)] =
      (zMaskGarbleEquiv c0 coefficients input (zMaskSource randomness oracles key)).1.2 := by
  dsimp only
  simp only [digitGarble_selectedOutputs_eq, digitGarble_bitsK_eq]
  rfl

def zMaskPivotShift (amount : BaseField) (view : ZMaskView) : ZMaskView :=
  (view.1, Function.update view.2 4 (lowMaskShift amount (view.2 4)))

@[simp] theorem zMaskPivotShift_zero (view : ZMaskView) : zMaskPivotShift 0 view = view := by
  simp [zMaskPivotShift]

theorem zMaskPivotShift_add (first second : BaseField) (view : ZMaskView) :
    zMaskPivotShift first (zMaskPivotShift second view) = zMaskPivotShift (first + second) view := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases pivot : index = 4
    · subst index; simp [zMaskPivotShift, lowMaskShift_add]
    · simp [zMaskPivotShift, pivot]

theorem zMaskResult_pivotShift (input : AffineInput) (amount : BaseField) (view : ZMaskView) :
    zMaskResult input (zMaskPivotShift amount view) = zMaskResult input view + amount := by
  change view.1 0 + (view.1 1 * input.y + view.1 2 * input.x * input.y +
    view.1 3 * input.x ^ 2 + view.1 4 * input.y ^ 2 +
    DigitAdaptor.fromBits (view.2 0) * input.x + DigitAdaptor.fromBits (view.2 3) * input.x +
    DigitAdaptor.fromBits (view.2 1) * input.y +
    DigitAdaptor.fromBits (lowMaskShift amount (view.2 4)) + DigitAdaptor.fromBits (view.2 2)) =
    view.1 0 + (view.1 1 * input.y + view.1 2 * input.x * input.y +
    view.1 3 * input.x ^ 2 + view.1 4 * input.y ^ 2 +
    DigitAdaptor.fromBits (view.2 0) * input.x + DigitAdaptor.fromBits (view.2 3) * input.x +
    DigitAdaptor.fromBits (view.2 1) * input.y +
    DigitAdaptor.fromBits (view.2 4) + DigitAdaptor.fromBits (view.2 2)) + amount
  rw [fromBits_lowMaskShift]
  ring

theorem BiquadraticZRequest.retarget_maskView (request : BiquadraticZRequest)
    (input : AffineInput) (target : BaseField) :
    (request.retarget input target).maskView =
      zMaskPivotShift (target - zMaskResult input request.maskView) request.maskView := by
  apply Prod.ext
  · rfl
  · funext index
    fin_cases index
    · rfl
    · rfl
    · rfl
    · rfl
    · change retargetBits request.x9Targets
        (target - request.result input + DigitAdaptor.fromBits request.x9Targets) =
          lowMaskShift (target - zMaskResult input request.maskView) request.x9Targets
      rw [lowMaskShift_eq_retargetBits, ← request.result_eq_zMaskResult input]
      apply congrArg (retargetBits request.x9Targets)
      ring

/-- Real Z masks and the corrected simulator give the same complete polynomial view. -/
theorem zMaskGarble_eq_retargetDistribution (c0 : BaseField)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype ZMaskData).map
      (fun source => (zMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype ZMaskView).map (fun view =>
      zMaskPivotShift (zMaskPolynomial c0 coefficients input - zMaskResult input view) view) := by
  let e := zMaskGarbleEquiv c0 coefficients input
  letI : Nonempty {view : ZMaskView //
      zMaskResult input view = zMaskPolynomial c0 coefficients input} := ⟨e (0, 0)⟩
  rw [map_uniform_retargetOfShift (zMaskResult input) zMaskPivotShift
    zMaskPivotShift_zero zMaskPivotShift_add (zMaskResult_pivotShift input),
    ← map_uniformOfFintype_equivBetween e, PMF.map_comp]
  rfl

attribute [local instance] bitAdaptorTableFintype publicVectorFintype

/-- This sample keeps every table row and lift quotient outside the field-mask view. -/
abbrev BiquadraticSampleRemainder (count : Nat) :=
  (Fin count → Vector BitAdaptor.Table coordinateBitCount) ×
    (Fin count → Fin coordinateBitCount → HashLiftQuotient)

local instance (count : Nat) : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty XPublicSample := ⟨defaultRowPublicSample.x⟩
local instance : Nonempty YPublicSample := ⟨defaultRowPublicSample.y⟩
local instance : Nonempty ZPublicSample := ⟨defaultRowPublicSample.z⟩

/-- This equivalence preserves all X sample fields in two independent groups. -/
def xSampleViewEquiv : XPublicSample ≃ XMaskView × BiquadraticSampleRemainder 4 where
  toFun sample := ((sample.coefficients, sample.targets), (sample.tables, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    targets := pair.1.2
    tables := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

def ySampleViewEquiv : YPublicSample ≃ YMaskView × BiquadraticSampleRemainder 3 where
  toFun sample := ((sample.coefficients, sample.targets), (sample.tables, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    targets := pair.1.2
    tables := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

def zSampleViewEquiv : ZPublicSample ≃ ZMaskView × BiquadraticSampleRemainder 5 where
  toFun sample := ((sample.coefficients, sample.targets), (sample.tables, sample.quotients))
  invFun pair := {
    coefficients := pair.1.1
    targets := pair.1.2
    tables := pair.2.1
    quotients := pair.2.2 }
  left_inv sample := by cases sample; rfl
  right_inv _ := rfl

theorem map_uniform_xSampleViewEquiv :
    (PMF.uniformOfFintype XPublicSample).map xSampleViewEquiv =
      PMF.uniformOfFintype (XMaskView × BiquadraticSampleRemainder 4) :=
  map_uniformOfFintype_equivBetween xSampleViewEquiv

theorem map_uniform_ySampleViewEquiv :
    (PMF.uniformOfFintype YPublicSample).map ySampleViewEquiv =
      PMF.uniformOfFintype (YMaskView × BiquadraticSampleRemainder 3) :=
  map_uniformOfFintype_equivBetween ySampleViewEquiv

theorem map_uniform_zSampleViewEquiv :
    (PMF.uniformOfFintype ZPublicSample).map zSampleViewEquiv =
      PMF.uniformOfFintype (ZMaskView × BiquadraticSampleRemainder 5) :=
  map_uniformOfFintype_equivBetween zSampleViewEquiv

theorem map_uniform_xSampleView :
    (PMF.uniformOfFintype XPublicSample).map (fun sample => sample.request.maskView) =
      PMF.uniformOfFintype XMaskView := by
  have projection : (fun sample : XPublicSample => sample.request.maskView) =
      Prod.fst ∘ xSampleViewEquiv := by
    funext sample
    apply Prod.ext <;> funext index <;> fin_cases index <;> rfl
  rw [projection]
  have law := congrArg (fun distribution => distribution.map Prod.fst) map_uniform_xSampleViewEquiv
  simpa only [PMF.map_comp, map_uniform_prod_fst] using law

theorem map_uniform_ySampleView :
    (PMF.uniformOfFintype YPublicSample).map (fun sample => sample.request.maskView) =
      PMF.uniformOfFintype YMaskView := by
  have projection : (fun sample : YPublicSample => sample.request.maskView) =
      Prod.fst ∘ ySampleViewEquiv := by
    funext sample
    apply Prod.ext <;> funext index <;> fin_cases index <;> rfl
  rw [projection]
  have law := congrArg (fun distribution => distribution.map Prod.fst) map_uniform_ySampleViewEquiv
  simpa only [PMF.map_comp, map_uniform_prod_fst] using law

theorem map_uniform_zSampleView :
    (PMF.uniformOfFintype ZPublicSample).map (fun sample => sample.request.maskView) =
      PMF.uniformOfFintype ZMaskView := by
  have projection : (fun sample : ZPublicSample => sample.request.maskView) =
      Prod.fst ∘ zSampleViewEquiv := by
    funext sample
    apply Prod.ext <;> funext index <;> fin_cases index <;> rfl
  rw [projection]
  have law := congrArg (fun distribution => distribution.map Prod.fst) map_uniform_zSampleViewEquiv
  simpa only [PMF.map_comp, map_uniform_prod_fst] using law

/-- This law uses the actual XPublicSample sampler and request retarget operation. -/
theorem xMaskGarble_eq_publicSampleRetarget (c0 : BaseField)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype XMaskData).map
      (fun source => (xMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype XPublicSample).map (fun sample =>
      (sample.request.retarget input (xMaskPolynomial c0 coefficients input)).maskView) := by
  rw [xMaskGarble_eq_retargetDistribution, ← map_uniform_xSampleView, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype XPublicSample).map)
  funext sample
  exact (sample.request.retarget_maskView input _).symm

theorem yMaskGarble_eq_publicSampleRetarget (c0 : BaseField)
    (coefficients : Fin 3 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype YMaskData).map
      (fun source => (yMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype YPublicSample).map (fun sample =>
      (sample.request.retarget input (yMaskPolynomial c0 coefficients input)).maskView) := by
  rw [yMaskGarble_eq_retargetDistribution, ← map_uniform_ySampleView, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype YPublicSample).map)
  funext sample
  exact (sample.request.retarget_maskView input _).symm

theorem zMaskGarble_eq_publicSampleRetarget (c0 : BaseField)
    (coefficients : Fin 4 → BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype ZMaskData).map
      (fun source => (zMaskGarbleEquiv c0 coefficients input source).1) =
    (PMF.uniformOfFintype ZPublicSample).map (fun sample =>
      (sample.request.retarget input (zMaskPolynomial c0 coefficients input)).maskView) := by
  rw [zMaskGarble_eq_retargetDistribution, ← map_uniform_zSampleView, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype ZPublicSample).map)
  funext sample
  exact (sample.request.retarget_maskView input _).symm

end

end Kriterion.ArgoMAC.Security
