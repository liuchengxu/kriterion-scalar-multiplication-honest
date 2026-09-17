import Proof.Privacy.Distribution.AdaptiveMaskDistribution
import Proof.Privacy.Distribution.OutputRowDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

/-- This view retains every tape value except the point offsets and row scales. -/
def actualOutputRest [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) : OutputRowRest :=
  outputRowRest (garblingRandomnessOffsetEquiv randomness).2

/-- Invalid inputs do not contribute output rows to the valid branch. -/
def actualSelectedOutput [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (randomness : Garbling.Randomness) :
    Option Result :=
  (decodePoint input).map fun _ => (actualOutputRowView scalar input randomness).1

/-- This view extends valid output rows to the full point-offset source. -/
def fullSelectedOutput [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput)
    (source : OffsetRandomness × GarblingOffsetRest) : Option Result :=
  (decodePoint input).map fun point => (mathematicalOutputRowView scalar input point source).1

/-- This view uses the simulator's output targets for each valid selected input. -/
def idealSelectedOutput [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (source : OutputRowSource) : Option Result :=
  (decodePoint input).map fun point =>
    (outputTargetView input (scalarMultiplication scalar point) source).1

/-- The scale equivalence uses the selected input only on the valid branch. -/
def selectedOutputNormalization [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) : Garbling.Randomness ≃ Garbling.Randomness :=
  match decoded : decodePoint input with
  | none => Equiv.refl _
  | some point => normalizeGarblingRhos scalar input point decoded

/-- The scale equivalence retains the actual oracle coin. -/
theorem selectedOutputNormalization_rest [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (randomness : Garbling.Randomness) :
    actualOutputRest (selectedOutputNormalization scalar input randomness) =
      actualOutputRest randomness := by
  unfold selectedOutputNormalization
  split
  · rfl
  · rename_i point decoded
    simp only [actualOutputRest, normalizeGarblingRhos_split]
    exact outputRowRest_normalize (outputKeys construction scalar randomness.offsets)
      (garblingRandomnessOffsetEquiv randomness).2 input point decoded

private theorem pointEmbed_rest [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) :
    outputRowRest (nonzeroPointTapeEmbed construction
      (garblingRandomnessPointEquiv construction randomness)).2 = actualOutputRest randomness := rfl

/-- The selected scale equivalence gives the full point rows and keeps the rest. -/
theorem actualSelectedOutput_normalize [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (randomness : Garbling.Randomness) :
    actualSelectedOutput scalar input randomness =
      fullSelectedOutput scalar input
        (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction
          (selectedOutputNormalization scalar input randomness))) := by
  unfold actualSelectedOutput fullSelectedOutput selectedOutputNormalization
  split <;> rename_i decoded
  · simp only [decoded, Option.map_none]
  · simp only [decoded, Option.map_some]
    exact congrArg (fun pair : Result × OutputRowRest => some pair.1)
      (actualOutputRowView_normalize scalar input _ decoded randomness)

/-- This reindex uses the selected valid point and keeps every other tape value. -/
def selectedOutputReindex [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) :
    (OffsetRandomness × GarblingOffsetRest) ≃ (OffsetRandomness × GarblingOffsetRest) :=
  match decodePoint input with
  | none => Equiv.refl _
  | some point => Equiv.prodCongr (construction.offsetEquiv scalar point) (Equiv.refl _)

theorem selectedOutputReindex_rest [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) (source : OffsetRandomness × GarblingOffsetRest) :
    (selectedOutputReindex scalar input source).2 = source.2 := by
  unfold selectedOutputReindex
  split <;> rfl

/-- The selected point reindex gives the exact simulator target rows. -/
theorem fullSelectedOutput_reindex [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    (scalar : ScalarField) (input : AffineInput) (source : OffsetRandomness × GarblingOffsetRest) :
    fullSelectedOutput scalar input source =
      idealSelectedOutput scalar input (outputRowSourceEquiv
        (selectedOutputReindex scalar input source)) := by
  unfold fullSelectedOutput idealSelectedOutput selectedOutputReindex
  split <;> rename_i decoded
  · simp only [decoded, Option.map_none]
  · simp only [decoded, Option.map_some]
    exact congrArg (fun pair : Result × OutputRowRest => some pair.1)
      ((mathematicalOutputRowView_reindex scalar input _ source).trans
        (simulatedOutputRowView_source input _ _))

/-- The preserved-view law also retains any later randomized observation. -/
theorem uniform_bind_viewEquiv_observe {A B View Choice Observation : Type*}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (equivalences : Choice → A ≃ B) (viewA : A → View) (viewB : B → View)
    (preserved : ∀ choice value, viewB (equivalences choice value) = viewA value)
    (choose : View → PMF Choice) (observe : Choice → B → PMF Observation) :
    (PMF.uniformOfFintype A).bind (fun value =>
      (choose (viewA value)).bind (fun choice => observe choice (equivalences choice value))) =
    (PMF.uniformOfFintype B).bind (fun value =>
      (choose (viewB value)).bind (fun choice => observe choice value)) := by
  have same := congrArg (fun distribution => distribution.bind
    (fun pair : Choice × B => observe pair.1 pair.2))
    (uniform_bind_viewEquiv equivalences viewA viewB preserved choose)
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using same

attribute [local instance] vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype

/-- Adaptive scale normalization retains the selected input and auxiliary state. -/
theorem adaptiveOutput_normalize [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Garbling.Randomness)
    (parameter : Nat) (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (choose (actualOutputRest randomness)).bind (fun selected =>
        observe selected (actualSelectedOutput scalar selected.1 randomness)
          (actualOutputRest randomness))) =
    (randomTape witness parameter).bind (fun randomness =>
      (choose (actualOutputRest randomness)).bind (fun selected =>
        observe selected (fullSelectedOutput scalar selected.1
          (nonzeroPointTapeEmbed construction
            (garblingRandomnessPointEquiv construction randomness)))
          (actualOutputRest randomness))) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  have same := uniform_bind_viewEquiv_observe
    (fun selected : AffineInput × Aux => selectedOutputNormalization scalar selected.1)
    actualOutputRest actualOutputRest
    (fun selected => selectedOutputNormalization_rest scalar selected.1) choose
    (fun selected randomness => observe selected (fullSelectedOutput scalar selected.1
      (nonzeroPointTapeEmbed construction
        (garblingRandomnessPointEquiv construction randomness))) (actualOutputRest randomness))
  simpa only [← actualSelectedOutput_normalize, selectedOutputNormalization_rest, randomTape] using same

private theorem outputRowSourceEquiv_rest [FieldCertificate]
    (source : OffsetRandomness × GarblingOffsetRest) :
    (outputRowSourceEquiv source).2.2 = outputRowRest source.2 := rfl

/-- Adaptive point reindexing gives the simulator target source and retains the oracle coin. -/
theorem adaptiveOutput_reindex [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).bind (fun source =>
      (choose (outputRowRest source.2)).bind (fun selected =>
        observe selected (fullSelectedOutput scalar selected.1 source) (outputRowRest source.2))) =
    (PMF.uniformOfFintype OutputRowSource).bind (fun source =>
      (choose source.2.2).bind (fun selected =>
        observe selected (idealSelectedOutput scalar selected.1 source) source.2.2)) := by
  have same := uniform_bind_viewEquiv_observe
    (fun selected : AffineInput × Aux =>
      (selectedOutputReindex scalar selected.1).trans outputRowSourceEquiv)
    (fun source => outputRowRest source.2) (fun source => source.2.2)
    (fun selected source => by
      simp only [Equiv.trans_apply, outputRowSourceEquiv_rest, selectedOutputReindex_rest])
    choose (fun selected source =>
      observe selected (idealSelectedOutput scalar selected.1 source) source.2.2)
  simpa only [Equiv.trans_apply, ← fullSelectedOutput_reindex,
    outputRowSourceEquiv_rest, selectedOutputReindex_rest] using same

/-- The valid adaptive row law costs only the nonidentity-offset restriction. -/
theorem adaptiveOutput_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype OutputRowSource).bind (fun source =>
        (choose source.2.2).bind (fun selected =>
          observe selected (idealSelectedOutput scalar selected.1 source)
            source.2.2))).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        (choose (actualOutputRest randomness)).bind (fun selected =>
          observe selected (actualSelectedOutput scalar selected.1 randomness)
            (actualOutputRest randomness)))).toOuterMeasure event).toReal| ≤
        (2 : ℝ) ^ (-240 : ℤ) := by
  rw [← adaptiveOutput_reindex scalar choose observe,
    adaptiveOutput_normalize scalar witness parameter choose observe]
  exact randomTape_point_observation_bound construction witness parameter
    (fun source => (choose (outputRowRest source.2)).bind (fun selected =>
      observe selected (fullSelectedOutput scalar selected.1 source) (outputRowRest source.2))) event

attribute [local instance] circuitMaskSampleFintype

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩

/-- This operation inserts valid output rows and keeps the actual bridge key. -/
def retargetOutput (sample : PublicSample) (input : AffineInput)
    (result : Option Result) (rest : OutputRowRest) : Option PublicSample :=
  result.map fun value => sample.retargetMask input rest.2.1.bridgeKey value.pointMacs

private theorem validCurveTarget [FieldCertificate] (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (key mask : BaseField) :
    key + mask * (input.x ^ 3 + 3 - input.y ^ 2) = key := by
  have valid := (decodePoint_defined input).mp (by rw [decoded]; simp)
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 from sub_eq_zero.mpr valid.symm]
  simp

private theorem retarget_actualSelectedOutput [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (randomness : Garbling.Randomness)
    (input : AffineInput) (sample : PublicSample) :
    (decodePoint input).map (fun _ => sample.retargetMask input
      (randomness.bridgeKey + randomness.curveMask.value * (input.x ^ 3 + 3 - input.y ^ 2))
      (evaluateRowsCubic (rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
        randomness.pointRandomness) input)) =
    retargetOutput sample input (actualSelectedOutput scalar input randomness)
      (actualOutputRest randomness) := by
  unfold retargetOutput actualSelectedOutput
  cases decoded : decodePoint input with
  | none => rfl
  | some point =>
      have onCurve : OnCurve input := (decodePoint_defined input).mp (by rw [decoded]; simp)
      simp only [Option.map_some, validCurveTarget input point decoded,
        evaluateRowsCubic_eq _ (rowsForOutputKeysSparse _ _) input onCurve]
      rfl

/-- This hybrid uses the exact actual rows before the selected input is known. -/
def actualAdaptiveMaskRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      OutputRowRest → PMF Observation) : PMF Observation :=
  let rows := rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
    randomness.pointRandomness
  (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
    let table := circuitMaskSourceTable randomness.bridgeKey randomness.curveMask.value rows source
    (choose table (actualOutputRest randomness)).bind fun selected =>
      observe table selected ((decodePoint selected.1).map fun _ =>
        circuitMaskSampleGarble randomness.bridgeKey randomness.curveMask.value rows selected.1 source)
        (actualOutputRest randomness)

/-- The mask transport makes adaptive selection independent of the output offsets and scales. -/
theorem actualAdaptiveMaskRun_retarget [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (randomness : Garbling.Randomness)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      OutputRowRest → PMF Observation) :
    actualAdaptiveMaskRun scalar randomness choose observe =
    (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample) (actualOutputRest randomness)).bind fun selected =>
        observe (publicMaskTable sample) selected
          (retargetOutput sample selected.1 (actualSelectedOutput scalar selected.1 randomness)
            (actualOutputRest randomness)) (actualOutputRest randomness)) := by
  let rows := rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
    randomness.pointRandomness
  have same := congrArg (fun distribution => distribution.bind
    (fun pair : (AffineInput × Aux) × PublicSample =>
      observe (publicMaskTable pair.2) pair.1 ((decodePoint pair.1.1).map fun _ => pair.2)
        (actualOutputRest randomness)))
    (adaptiveCircuitMaskGarble_eq_retarget randomness.bridgeKey randomness.curveMask.value rows
      (rowsForOutputKeysSparse _ _) (fun table => choose table (actualOutputRest randomness)))
  have table (input : AffineInput) (source : CircuitMaskSample) :
      publicMaskTable (circuitMaskSampleGarble randomness.bridgeKey
        randomness.curveMask.value rows input source) =
      circuitMaskSourceTable randomness.bridgeKey randomness.curveMask.value rows source :=
    circuitMaskSampleGarble_table_input _ _ _ _ input ⟨0, 0⟩
  simp only [PMF.bind_bind, PMF.bind_map] at same
  dsimp only [Function.comp_def] at same
  simp only [table, publicMaskTable_retarget] at same
  simpa only [rows, retarget_actualSelectedOutput, actualAdaptiveMaskRun] using same

private theorem bind_tagged {Input Sample Aux Output Observation : Type*}
    (samples : PMF Sample) (choose : Sample → PMF (Input × Aux))
    (output : Input → Output) (observe : Sample → (Input × Aux) → Output → PMF Observation) :
    (samples.bind (fun sample => (choose sample).map fun selected =>
      (selected.1, sample, selected.2))).bind (fun selected =>
        observe selected.2.1 (selected.1, selected.2.2) (output selected.1)) =
    samples.bind (fun sample => (choose sample).bind fun selected =>
      observe sample selected (output selected.1)) := by
  rw [PMF.bind_bind]
  apply congrArg samples.bind
  funext sample
  rw [PMF.bind_map]
  rfl

/-- This bound preserves the public table, the auxiliary state, and the actual oracle coin. -/
theorem adaptiveMaskOutput_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → OutputRowRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → Option PublicSample →
      OutputRowRest → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype OutputRowSource).bind (fun source =>
        (PMF.uniformOfFintype PublicSample).bind (fun sample =>
          (choose (publicMaskTable sample) source.2.2).bind fun selected =>
            observe (publicMaskTable sample) selected
              (retargetOutput sample selected.1 (idealSelectedOutput scalar selected.1 source)
                source.2.2) source.2.2))).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind (fun randomness =>
        actualAdaptiveMaskRun scalar randomness choose observe)).toOuterMeasure event).toReal| ≤
      (2 : ℝ) ^ (-240 : ℤ) := by
  simp_rw [actualAdaptiveMaskRun_retarget]
  have bound := adaptiveOutput_observation_bound scalar witness parameter
    (fun rest => (PMF.uniformOfFintype PublicSample).bind (fun sample =>
      (choose (publicMaskTable sample) rest).map fun selected =>
        (selected.1, sample, selected.2)))
    (fun selected result rest => observe (publicMaskTable selected.2.1)
      (selected.1, selected.2.2) (retargetOutput selected.2.1 selected.1 result rest) rest) event
  have idealTagged (source : OutputRowSource) := bind_tagged
    (PMF.uniformOfFintype PublicSample) (fun sample => choose (publicMaskTable sample) source.2.2)
    (fun input => idealSelectedOutput scalar input source)
    (fun sample selected result => observe (publicMaskTable sample) selected
      (retargetOutput sample selected.1 result source.2.2) source.2.2)
  have actualTagged (randomness : Garbling.Randomness) := bind_tagged
    (PMF.uniformOfFintype PublicSample)
    (fun sample => choose (publicMaskTable sample) (actualOutputRest randomness))
    (fun input => actualSelectedOutput scalar input randomness)
    (fun sample selected result => observe (publicMaskTable sample) selected
      (retargetOutput sample selected.1 result (actualOutputRest randomness))
        (actualOutputRest randomness))
  simp only [idealTagged, actualTagged] at bound
  exact bound

/-- The source separates the simulator's actual free-point coin from the retained tape. -/
def outputEncodingSourceEquiv [FieldCertificate] :
    OutputRowSource ≃ ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase)) × OutputRowRest :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr (Equiv.prodCongr vectorFunctionEquiv.symm (Equiv.refl _)) (Equiv.refl _))

/-- The target sampler uses the exact free-point and scale coin of simulateEncode. -/
theorem idealOutput_encodingSource [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (PMF.uniformOfFintype OutputRowSource).bind (fun source =>
      (choose source.2.2).bind (fun selected =>
        observe selected (idealSelectedOutput scalar selected.1 source) source.2.2)) =
    (PMF.uniformOfFintype OutputRowRest).bind (fun rest =>
      (choose rest).bind (fun selected =>
        (PMF.uniformOfFintype
          ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
          observe selected ((decodePoint selected.1).map fun point =>
            ⟨selected.1, outputTargets (scalarMultiplication scalar point)
              (Vector.ofFn coin.1) coin.2⟩) rest)) := by
  have source := map_uniformOfFintype_equivBetween outputEncodingSourceEquiv.symm
  rw [← source, PMF.bind_map, uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map]
  apply congrArg ((PMF.uniformOfFintype OutputRowRest).bind)
  funext rest
  rw [PMF.bind_comm]
  rfl

end

end Kriterion.ArgoMAC.Security
