import Proof.Privacy.Source.ActualMaskSource

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- This view contains the actual public pipeline table. -/
def publicMaskTable (sample : PublicSample) : Pipeline.Table :=
  ⟨sample.curveRequest.table, pointGateTable sample.pointRequests⟩

/-- Retargeting preserves the whole public table. -/
theorem publicMaskTable_retarget (sample : PublicSample) (input : AffineInput)
    (curveTarget : BaseField)
    (targets : Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount) :
    publicMaskTable (sample.retargetMask input curveTarget targets) = publicMaskTable sample := by
  simp only [publicMaskTable, PublicSample.retargetMask_curveRequest,
    PublicSample.retargetMask_pointRequests, CurveGateRequest.retarget_table,
    retargetPointGateRequests_table]

private theorem xMaskSampleGarble_table_input (row : Coordinates.Coefficients)
    (source : XMaskSample) (first second : AffineInput) :
    (xMaskSampleGarble row first source).request.table =
      (xMaskSampleGarble row second source).request.table := by
  dsimp only [xMaskSampleGarble, xSampleViewEquiv, Equiv.symm, Equiv.coe_fn_mk,
    XPublicSample.request, BiquadraticXRequest.table]
  simp only [xMaskGarbleEquiv_coefficients]

private theorem yMaskSampleGarble_table_input (row : Coordinates.Coefficients)
    (source : YMaskSample) (first second : AffineInput) :
    (yMaskSampleGarble row first source).request.table =
      (yMaskSampleGarble row second source).request.table := by
  dsimp only [yMaskSampleGarble, ySampleViewEquiv, Equiv.symm, Equiv.coe_fn_mk,
    YPublicSample.request, BiquadraticYRequest.table]
  simp only [yMaskGarbleEquiv_coefficients]

private theorem zMaskSampleGarble_table_input (row : Coordinates.Coefficients)
    (source : ZMaskSample) (first second : AffineInput) :
    (zMaskSampleGarble row first source).request.table =
      (zMaskSampleGarble row second source).request.table := by
  dsimp only [zMaskSampleGarble, zSampleViewEquiv, Equiv.symm, Equiv.coe_fn_mk,
    ZPublicSample.request, BiquadraticZRequest.table]
  simp only [zMaskGarbleEquiv_coefficients]

set_option maxRecDepth 10000 in
private theorem curveMaskSampleGarble_table_input (key mask : BaseField)
    (source : CurveMaskSample) (first second : AffineInput) :
    (curveMaskSampleGarble key mask first source).request.table =
      (curveMaskSampleGarble key mask second source).request.table := by
  have coefficients : (curveMaskViewEquiv key mask first source.1).1.1 =
      (curveMaskViewEquiv key mask second source.1).1.1 := by
    funext index
    refine Fin.cases ?_ ?_ index
    · rw [curveMaskViewEquiv_constant, curveMaskViewEquiv_constant]
    · intro index
      have tail (input : AffineInput) := congrArg (fun data : CurveMaskData => data.1 index)
        ((curveMaskFiberEquiv input (key + mask * (input.x ^ 3 + 3 - input.y ^ 2))).symm_apply_apply
          (curveMaskShiftEquiv mask input source.1))
      exact (tail first).trans (tail second).symm
  dsimp only [curveMaskSampleGarble, curveSampleViewEquiv, Equiv.symm, Equiv.coe_fn_mk,
    CurvePublicSample.request, CurveGateRequest.table]
  rw [coefficients]

private theorem rowMaskSampleGarble_table_input (rows : Coordinates.Rows)
    (source : RowMaskSample) (first second : AffineInput) :
    (rowMaskSampleGarble rows first source).request.table =
      (rowMaskSampleGarble rows second source).request.table := by
  dsimp only [rowMaskSampleGarble, RowPublicSample.request, BiquadraticRowRequest.table]
  rw [xMaskSampleGarble_table_input rows.x source.1 first second,
    yMaskSampleGarble_table_input rows.y source.2.1 first second,
    zMaskSampleGarble_table_input rows.z source.2.2 first second]

private theorem pointGateTable_congr (first second : PointGateRequests)
    (same : ∀ index, (first.get index).table = (second.get index).table) :
    pointGateTable first = pointGateTable second := by
  exact congrArg (fun tables : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.RowTable =>
    (⟨Vector.ofFn (fun index => (tables index).x),
      Vector.ofFn (fun index => (tables index).y),
      Vector.ofFn (fun index => (tables index).z)⟩ : FieldMacToECMac.Table)) (funext same)

/-- The actual circuit mask map publishes the same table for every selected input. -/
theorem circuitMaskSampleGarble_table_input (key mask : BaseField)
    (rows : FieldMacToECMac.Rows) (source : CircuitMaskSample) (first second : AffineInput) :
    publicMaskTable (circuitMaskSampleGarble key mask rows first source) =
      publicMaskTable (circuitMaskSampleGarble key mask rows second source) := by
  have curve := curveMaskSampleGarble_table_input key mask source.1 first second
  have points : pointGateTable (circuitMaskSampleGarble key mask rows first source).pointRequests =
      pointGateTable (circuitMaskSampleGarble key mask rows second source).pointRequests := by
    apply pointGateTable_congr
    intro index
    simp only [circuitMaskSampleGarble, PublicSample.pointRequests, Vector.get_map, Vector.get_ofFn]
    exact rowMaskSampleGarble_table_input (rows.get index) (source.2 index) first second
  exact congrArg₂ Pipeline.Table.mk curve points

/-- This source table does not depend on the later selected input. -/
def circuitMaskSourceTable (key mask : BaseField) (rows : FieldMacToECMac.Rows)
    (source : CircuitMaskSample) : Pipeline.Table :=
  publicMaskTable (circuitMaskSampleGarble key mask rows ⟨0, 0⟩ source)

/-- The source table agrees with the actual linked pipeline garbler. -/
theorem circuitMaskSourceTable_actual (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness) (bridgeKey r1 r2 : BaseField)
    (mask : NonZeroBase)
    (fixedOracle : Cryptography.PermutationOracle Pipeline.FixedKeyIndex Cryptography.Block)
    (encOracle : Cryptography.PermutationOracle EncPRF.PermutationIndex Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey)
    (quotients : CircuitMaskQuotients) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    circuitMaskSourceTable bridgeKey mask.value
      (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness)
      (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask.value r1 r2
        fixedOracle pointKey inputKey quotients) =
      Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2
        fixedOracle encOracle hashOracle inputKey :=
  actualCircuitMaskSample_pipelineTable outputKeys pointRandomness bridgeKey r1 r2 mask
    fixedOracle encOracle hashOracle inputKey quotients ⟨0, 0⟩

/-- Every result fiber retains the same public table. -/
theorem circuitMaskSampleSplit_table (key mask : BaseField) (rows : FieldMacToECMac.Rows)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (input : AffineInput) (sample : PublicSample) :
    circuitMaskSourceTable key mask rows (circuitMaskSampleSplit key mask rows input sample).2 =
      publicMaskTable sample := by
  unfold circuitMaskSourceTable
  rw [circuitMaskSampleGarble_table_input key mask rows _ ⟨0, 0⟩ input,
    circuitMaskSampleGarble_split key mask rows sparse, publicMaskTable_retarget]

/-- A preserved view can select its own change of variables. -/
def adaptiveViewEquiv {A B View Choice : Type*}
    (equivalences : Choice → A ≃ B) (viewA : A → View) (viewB : B → View)
    (preserved : ∀ choice value, viewB (equivalences choice value) = viewA value)
    (choose : View → Choice) : A ≃ B where
  toFun value := equivalences (choose (viewA value)) value
  invFun value := (equivalences (choose (viewB value))).symm value
  left_inv value := by
    dsimp only
    rw [preserved]
    exact Equiv.symm_apply_apply _ _
  right_inv value := by
    dsimp only
    have same := preserved (choose (viewB value))
      ((equivalences (choose (viewB value))).symm value)
    rw [Equiv.apply_symm_apply] at same
    rw [← same]
    exact Equiv.apply_symm_apply _ _

/-- This equivalence permits deterministic input selection from the actual public table. -/
def adaptiveCircuitMaskSplit (key mask : BaseField) (rows : FieldMacToECMac.Rows)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (choose : Pipeline.Table → AffineInput) : PublicSample ≃ CircuitMaskResults × CircuitMaskSample :=
  adaptiveViewEquiv (circuitMaskSampleSplit key mask rows) publicMaskTable
    (fun sample => circuitMaskSourceTable key mask rows sample.2)
    (circuitMaskSampleSplit_table key mask rows sparse) choose

private theorem map_choice_pair_apply {Choice Value : Type*} [DecidableEq Value]
    (choices : PMF Choice) (value : Choice → Value) (choice : Choice) (output : Value) :
    (choices.map (fun selected => (selected, value selected))) (choice, output) =
      if output = value choice then choices choice else 0 := by
  classical
  rw [PMF.map_apply, tsum_eq_single choice]
  · simp
  · intro other different
    simp [Ne.symm different]

/-- A randomized choice from a preserved view commutes with the uniform change of variables. -/
theorem uniform_bind_viewEquiv {A B View Choice : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (equivalences : Choice → A ≃ B) (viewA : A → View) (viewB : B → View)
    (preserved : ∀ choice value, viewB (equivalences choice value) = viewA value)
    (choose : View → PMF Choice) :
    (PMF.uniformOfFintype A).bind (fun value =>
      (choose (viewA value)).map (fun choice => (choice, equivalences choice value))) =
    (PMF.uniformOfFintype B).bind (fun value =>
      (choose (viewB value)).map (fun choice => (choice, value))) := by
  classical
  apply PMF.ext
  rintro ⟨choice, output⟩
  rw [PMF.bind_apply, PMF.bind_apply]
  simp only [map_choice_pair_apply]
  rw [tsum_eq_single ((equivalences choice).symm output), tsum_eq_single output]
  · have same := preserved choice ((equivalences choice).symm output)
    rw [Equiv.apply_symm_apply] at same
    simp only [Equiv.apply_symm_apply, ← same, PMF.uniformOfFintype_apply,
      Fintype.card_congr (equivalences choice)]
  · intro other different
    simp [Ne.symm different]
  · intro other different
    have unequal : equivalences choice other ≠ output := by
      intro equal
      exact different ((equivalences choice).injective
        (equal.trans ((equivalences choice).apply_symm_apply output).symm))
    simp [Ne.symm unequal]

attribute [local instance] bitAdaptorTableFintype publicVectorFintype ciphertextFintype
  xMaskSampleFintype yMaskSampleFintype zMaskSampleFintype curveMaskSampleFintype
  rowMaskSampleFintype circuitMaskSampleFintype

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩

/-- The input kernel can retain its state and transcript in the auxiliary value. -/
theorem adaptiveCircuitMaskSplit_uniform {Aux : Type*} (key mask : BaseField)
    (rows : FieldMacToECMac.Rows)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (choose : Pipeline.Table → PMF (AffineInput × Aux)) :
    (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample)).map (fun selected =>
        (selected, (circuitMaskSampleSplit key mask rows selected.1 sample).2))) =
    (PMF.uniformOfFintype CircuitMaskSample).bind (fun source =>
      (choose (circuitMaskSourceTable key mask rows source)).map (fun selected =>
        (selected, source))) := by
  have same := uniform_bind_viewEquiv
    (fun selected : AffineInput × Aux => circuitMaskSampleSplit key mask rows selected.1)
    publicMaskTable (fun pair => circuitMaskSourceTable key mask rows pair.2)
    (fun selected => circuitMaskSampleSplit_table key mask rows sparse selected.1) choose
  have projected := congrArg (fun distribution => distribution.map
    (fun pair : (AffineInput × Aux) × (CircuitMaskResults × CircuitMaskSample) =>
      (pair.1, pair.2.2))) same
  simp only [PMF.map_bind, PMF.map_comp] at projected
  change _ = (PMF.uniformOfFintype (CircuitMaskResults × CircuitMaskSample)).bind
    ((fun source => (choose (circuitMaskSourceTable key mask rows source)).map
      (fun selected => (selected, source))) ∘ Prod.snd) at projected
  rw [← PMF.bind_map, map_uniform_prod_snd] at projected
  exact projected

/-- Adaptive input selection preserves the exact law of all selected mask requests. -/
theorem adaptiveCircuitMaskGarble_eq_retarget {Aux : Type*} (key mask : BaseField)
    (rows : FieldMacToECMac.Rows)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index))
    (choose : Pipeline.Table → PMF (AffineInput × Aux)) :
    (PMF.uniformOfFintype CircuitMaskSample).bind (fun source =>
      (choose (circuitMaskSourceTable key mask rows source)).map (fun selected =>
        (selected, circuitMaskSampleGarble key mask rows selected.1 source))) =
    (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample)).map (fun selected =>
        (selected, sample.retargetMask selected.1
          (key + mask * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))
          (FieldMacToECMac.evaluateRowsCubic rows selected.1)))) := by
  have same := congrArg (fun distribution => distribution.map
    (fun pair : (AffineInput × Aux) × CircuitMaskSample =>
      (pair.1, circuitMaskSampleGarble key mask rows pair.1.1 pair.2)))
    (adaptiveCircuitMaskSplit_uniform key mask rows sparse choose)
  simp only [PMF.map_bind, PMF.map_comp] at same
  dsimp only [Function.comp_def] at same
  simp only [circuitMaskSampleGarble_split key mask rows sparse] at same
  exact same.symm

end

end Kriterion.ArgoMAC.Security
