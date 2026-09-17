import Proof.Privacy.Distribution.TapeDistribution
import Proof.Privacy.Distribution.ProjectiveDistribution
import Proof.Correctness.RCBComplete

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

/-- This row uses unit scale before normalization. -/
def unitOutputRow (key : OutputKey) (input : AffineInput) : HomogeneousValue :=
  evaluateRow (Coordinates.rows key.offset.coordinates (digitEndomorphismBase key.digit) 1) input

/-- Every row scale multiplies the same unit-scale homogeneous value. -/
theorem evaluateOutputRow_scale [FieldCertificate]
    (key : OutputKey) (input : AffineInput) (scale : NonZeroBase) :
    evaluateRow (Coordinates.rows key.offset.coordinates
        (digitEndomorphismBase key.digit) scale.value) input =
      scaleHomogeneous scale (unitOutputRow key input) := by
  unfold unitOutputRow
  cases digitEndomorphismBase key.digit <;>
    simp [evaluateRowsNone, evaluateRowsSome, scaleHomogeneous]

/-- The complete RCB law fixes the point represented by the unit-scale row. -/
theorem unitOutputRow_decode [FieldCertificate] [GroupCertificate]
    (key : OutputKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Garbling.decodeHomogeneous (unitOutputRow key input) =
      some (digitScalar key.digit • point + key.offset.point) :=
  RCBComplete.decodeEvaluateOutputKeyRow key
    { (Seed.randomness 0).pointRandomness.get ⟨0, by decide⟩ with rho := ⟨1, one_ne_zero⟩ }
    input point decoded

/-- This nonzero factor converts the actual row to the canonical point representative. -/
def outputRowFactor [FieldCertificate] [GroupCertificate]
    (key : OutputKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) : NonZeroBase :=
  Classical.choose (exists_homogeneous_scale (unitOutputRow key input)
    (digitScalar key.digit • point + key.offset.point) (unitOutputRow_decode key input point decoded))

theorem unitOutputRow_eq [FieldCertificate] [GroupCertificate]
    (key : OutputKey) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    unitOutputRow key input = homogeneousOfPoint
      (digitScalar key.digit • point + key.offset.point) (outputRowFactor key input point decoded) :=
  Classical.choose_spec (exists_homogeneous_scale (unitOutputRow key input)
    (digitScalar key.digit • point + key.offset.point) (unitOutputRow_decode key input point decoded))

/-- This split separates rho from all three coordinate randomizers. -/
def rowRandomnessSplit : RowRandomness ≃
    NonZeroBase × (Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) where
  toFun randomness := (randomness.rho, randomness.x, randomness.y, randomness.z)
  invFun sample := ⟨sample.1, sample.2.1, sample.2.2.1, sample.2.2.2⟩
  left_inv randomness := by cases randomness; rfl
  right_inv sample := by rcases sample with ⟨rho, x, y, z⟩; rfl

/-- This split separates all row scales from all coordinate randomizers. -/
def pointRandomnessSplit : Randomness ≃
    (Fin outputMacCount → NonZeroBase) ×
      (Fin outputMacCount → Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) where
  toFun randomness := ((fun index => (randomness.get index).rho),
    fun index => ((randomness.get index).x, (randomness.get index).y, (randomness.get index).z))
  invFun sample := Vector.ofFn fun index => rowRandomnessSplit.symm (sample.1 index, sample.2 index)
  left_inv randomness := by
    apply Vector.ext
    intro index bound
    simp only [Vector.getElem_ofFn, rowRandomnessSplit, Equiv.coe_fn_symm_mk]
    rfl
  right_inv sample := by simp [rowRandomnessSplit]

/-- This equivalence changes rho and retains all three coordinate masks. -/
def rowRhoEquiv [FieldCertificate] (factor : NonZeroBase) : RowRandomness ≃ RowRandomness where
  toFun randomness := { randomness with rho := nonzeroScaleMulEquiv factor randomness.rho }
  invFun randomness := { randomness with rho := (nonzeroScaleMulEquiv factor).symm randomness.rho }
  left_inv randomness := by cases randomness; simp
  right_inv randomness := by cases randomness; simp

/-- This equivalence normalizes all row scales and retains the coordinate masks. -/
def normalizeRowRandomness [FieldCertificate] [GroupCertificate]
    (keys : OutputKeys) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) : Randomness ≃ Randomness :=
  vectorFunctionEquiv.symm.trans ((Equiv.piCongrRight fun index =>
    rowRhoEquiv (outputRowFactor (keys.get index) input point decoded)).trans vectorFunctionEquiv)

theorem normalizeRowRandomness_get [FieldCertificate] [GroupCertificate]
    (keys : OutputKeys) (randomness : Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (index : Fin outputMacCount) :
    (normalizeRowRandomness keys input point decoded randomness).get index =
      rowRhoEquiv (outputRowFactor (keys.get index) input point decoded) (randomness.get index) := by
  simp [normalizeRowRandomness, vectorFunctionEquiv]

/-- The actual output rows use canonical representatives after scale normalization. -/
theorem evaluateRows_normalize [FieldCertificate] [GroupCertificate]
    (keys : OutputKeys) (randomness : Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    evaluateRows (rowsForOutputKeys keys randomness) input =
      Vector.ofFn (fun index => homogeneousOfPoint
        (digitScalar (keys.get index).digit • point + (keys.get index).offset.point)
        ((normalizeRowRandomness keys input point decoded randomness).get index).rho) := by
  apply Vector.ext
  intro index bound
  simp only [evaluateRows, rowsForOutputKeys, Vector.getElem_ofFn, Vector.get_ofFn]
  rw [normalizeRowRandomness_get, evaluateOutputRow_scale, unitOutputRow_eq _ _ point decoded,
    scaleHomogeneous_representative]
  rfl

attribute [local instance] vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype

instance pointRandomnessNonempty : Nonempty Randomness := ⟨(Seed.randomness 0).pointRandomness⟩

instance rowMaskRandomnessNonempty :
    Nonempty (Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) :=
  ⟨((Seed.randomness 0).pointRandomness.get ⟨0, by decide⟩).x,
    ((Seed.randomness 0).pointRandomness.get ⟨0, by decide⟩).y,
    ((Seed.randomness 0).pointRandomness.get ⟨0, by decide⟩).z⟩

/-- The actual uniform row tape has independent scales and coordinate randomizers. -/
theorem map_uniform_pointRandomnessSplit [FieldCertificate] :
    (PMF.uniformOfFintype Randomness).map pointRandomnessSplit =
      PMF.uniformOfFintype
        ((Fin outputMacCount → NonZeroBase) ×
          (Fin outputMacCount → Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness)) :=
  uniform_map_equiv pointRandomnessSplit

/-- This type retains the coordinate masks, field data, and oracle data. -/
abbrev OutputRowRest :=
  (Fin outputMacCount → Biquadratic.XRandomness × Biquadratic.YRandomness × Biquadratic.ZRandomness) ×
    GarblingFieldData × GarblingOracleData

def outputRowRest (sample : GarblingOffsetRest) : OutputRowRest :=
  ((fun index => ((sample.1.get index).x, (sample.1.get index).y, (sample.1.get index).z)), sample.2)

/-- Scale normalization retains every coordinate mask. -/
theorem outputRowRest_normalize [FieldCertificate] [GroupCertificate]
    (keys : OutputKeys) (sample : GarblingOffsetRest) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    outputRowRest (normalizeRowRandomness keys input point decoded sample.1, sample.2) =
      outputRowRest sample := by
  dsimp only [outputRowRest]
  apply Prod.ext
  · funext index
    simpa only [rowRhoEquiv, Equiv.coe_fn_mk] using
      congrArg (fun row : RowRandomness => (row.x, row.y, row.z))
        (normalizeRowRandomness_get keys sample.1 input point decoded index)
  · rfl

/-- This vector contains the mathematical point outputs. -/
def outputPointVector [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (offsets : OffsetRandomness) (point : Point) :
    Vector Point outputMacCount :=
  ⟨(construction.outputs scalar offsets point).toArray, by
    simpa [outputMacCount] using construction.outputCount scalar offsets point⟩

/-- The actual output keys give the mathematical point outputs. -/
theorem outputPointVector_eq [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (offsets : ClampedAffineOffsets) (point : Point) :
    (Vector.ofFn fun index =>
      digitScalar ((outputKeys construction scalar offsets.1).get index).digit • point +
        ((outputKeys construction scalar offsets.1).get index).offset.point) =
      outputPointVector scalar (clampedPointOffsets construction offsets).1 point := by
  apply Vector.toList_inj.mp
  simpa only [outputPointVector, Vector.toList_mk, List.toList_toArray,
    clampedPointOffsets, RCBComplete.successfulOffsetRandomness] using RCBComplete.outputKeyPoints scalar offsets.1 offsets.2 point

/-- This function represents mathematical point rows with the sampled scales. -/
def mathematicalOutputRows [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (point : Point) (sample : OffsetRandomness × GarblingOffsetRest) :
    Vector HomogeneousValue outputMacCount :=
  Vector.ofFn fun index => homogeneousOfPoint
    ((outputPointVector scalar sample.1 point).get index) ((sample.2.1.get index).rho)

theorem evaluateRows_mathematical [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (offsets : ClampedAffineOffsets) (sample : GarblingOffsetRest)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    evaluateRows (rowsForOutputKeys (outputKeys construction scalar offsets.1) sample.1) input =
      mathematicalOutputRows scalar point ((clampedPointOffsets construction offsets).1,
        normalizeRowRandomness (outputKeys construction scalar offsets.1)
          input point decoded sample.1, sample.2) := by
  rw [evaluateRows_normalize _ _ _ point decoded]
  have points := outputPointVector_eq scalar offsets point
  simpa only [mathematicalOutputRows, Vector.get_ofFn] using
    congrArg (fun values : Vector Point outputMacCount => Vector.ofFn fun index =>
      homogeneousOfPoint (values.get index)
        ((normalizeRowRandomness (outputKeys construction scalar offsets.1)
          input point decoded sample.1).get index).rho) points

/-- This equivalence normalizes the actual tape and retains all other values. -/
def normalizeGarblingRhos [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) : Garbling.Randomness ≃ Garbling.Randomness :=
  garblingRandomnessOffsetEquiv.trans ((Equiv.prodCongrRight fun offsets : ClampedAffineOffsets =>
    Equiv.prodCongr (normalizeRowRandomness (outputKeys construction scalar offsets.1)
      input point decoded) (Equiv.refl (GarblingFieldData × GarblingOracleData))).trans
        garblingRandomnessOffsetEquiv.symm)

theorem normalizeGarblingRhos_split [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (randomness : Garbling.Randomness) :
    garblingRandomnessOffsetEquiv (normalizeGarblingRhos scalar input point decoded randomness) =
      ((garblingRandomnessOffsetEquiv randomness).1,
        normalizeRowRandomness (outputKeys construction scalar randomness.offsets)
          input point decoded randomness.pointRandomness,
        (garblingRandomnessOffsetEquiv randomness).2.2) := by
  simp only [normalizeGarblingRhos, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- This view contains the actual expected rows and the retained tape values. -/
def actualOutputRowView [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (randomness : Garbling.Randomness) :
    Result × OutputRowRest :=
  (expectedResult (rowsForOutputKeys (outputKeys construction scalar randomness.offsets)
    randomness.pointRandomness) input, outputRowRest (garblingRandomnessOffsetEquiv randomness).2)

/-- This view permits identity offsets after the row calculation. -/
def mathematicalOutputRowView [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (sample : OffsetRandomness × GarblingOffsetRest) : Result × OutputRowRest :=
  (⟨input, mathematicalOutputRows scalar point sample⟩, outputRowRest sample.2)

theorem actualOutputRowView_normalize [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (randomness : Garbling.Randomness) :
    actualOutputRowView scalar input randomness =
      mathematicalOutputRowView scalar input point
        (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction
          (normalizeGarblingRhos scalar input point decoded randomness))) := by
  simp only [garblingRandomnessPointEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    nonzeroPointTapeEmbed, normalizeGarblingRhos_split, actualOutputRowView,
    mathematicalOutputRowView, expectedResult]
  apply Prod.ext
  · exact congrArg (Result.mk input) (evaluateRows_mathematical scalar
      (garblingRandomnessOffsetEquiv randomness).1 (garblingRandomnessOffsetEquiv randomness).2
      input point decoded)
  · exact (outputRowRest_normalize (outputKeys construction scalar randomness.offsets)
      (garblingRandomnessOffsetEquiv randomness).2 input point decoded).symm

/-- The scale change preserves the actual uniform tape law. -/
theorem map_randomTape_actualOutputRowView [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (witness : Garbling.Randomness) (parameter : Nat) :
    (randomTape witness parameter).map (actualOutputRowView scalar input) =
      (randomTape witness parameter).map (fun randomness =>
        mathematicalOutputRowView scalar input point
          (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction randomness))) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  conv_lhs => arg 1; ext randomness; rw [actualOutputRowView_normalize scalar input point decoded]
  change (randomTape witness parameter).map
    ((fun randomness => mathematicalOutputRowView scalar input point
      (nonzeroPointTapeEmbed construction (garblingRandomnessPointEquiv construction randomness))) ∘
        normalizeGarblingRhos scalar input point decoded) = _
  rw [← PMF.map_comp]
  have invariant : (randomTape witness parameter).map
      (normalizeGarblingRhos scalar input point decoded) = randomTape witness parameter :=
    uniform_map_equiv (normalizeGarblingRhos scalar input point decoded)
  rw [invariant]

/-- This view uses the simulator's actual free point rows and scale function. -/
def simulatedOutputRowView [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (output : Point) (sample : OffsetRandomness × GarblingOffsetRest) :
    Result × OutputRowRest :=
  (⟨input, outputTargets output
    ⟨sample.1.freeOffsets.toArray, by simpa using sample.1.freeOffsetCount⟩
    (fun index => (sample.2.1.get index).rho)⟩, outputRowRest sample.2)

theorem mathematicalOutputRowView_reindex [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : ScalarField) (input : AffineInput) (point : Point)
    (sample : OffsetRandomness × GarblingOffsetRest) :
    mathematicalOutputRowView scalar input point sample =
      simulatedOutputRowView input (scalarMultiplication scalar point)
        (construction.offsetEquiv scalar point sample.1, sample.2) := by
  have points : outputPointVector scalar sample.1 point =
      (⟨(construction.simulatedOutputs (scalarMultiplication scalar point)
        (construction.offsetEquiv scalar point sample.1)).toArray, by
          simp [Construction.simulatedOutputs, outputMacCount,
            (construction.offsetEquiv scalar point sample.1).freeOffsetCount]⟩ :
        Vector Point outputMacCount) := by
    apply Vector.toList_inj.mp
    simpa only [outputPointVector, Vector.toList_mk, List.toList_toArray,
    clampedPointOffsets, RCBComplete.successfulOffsetRandomness] using
      construction.outputs_eq_simulatedOutputs_reindex scalar point sample.1
  unfold mathematicalOutputRowView simulatedOutputRowView mathematicalOutputRows outputTargets
  rw [points]
  rfl

/-- The full point-row distribution equals the actual simulator target distribution. -/
theorem map_uniform_mathematicalOutputRowView [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : ScalarField) (input : AffineInput) (point : Point) :
    (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map
      (mathematicalOutputRowView scalar input point) =
    (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map
      (simulatedOutputRowView input (scalarMultiplication scalar point)) := by
  conv_lhs => arg 1; ext sample; rw [mathematicalOutputRowView_reindex]
  change (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map
    (simulatedOutputRowView input (scalarMultiplication scalar point) ∘
      Equiv.prodCongr (construction.offsetEquiv scalar point) (Equiv.refl GarblingOffsetRest)) = _
  rw [← PMF.map_comp, uniform_map_equiv]

/-- This source separates the free points, row scales, and retained tape values. -/
abbrev OutputRowSource [FieldCertificate] :=
  Vector Point 90 × (Fin outputMacCount → NonZeroBase) × OutputRowRest

instance outputRowRestNonempty : Nonempty OutputRowRest :=
  Nonempty.map outputRowRest inferInstance

def outputRowSourceEquiv [FieldCertificate] :
    (OffsetRandomness × GarblingOffsetRest) ≃ OutputRowSource :=
  Equiv.prodCongr (offsetFunctionEquiv.symm.trans vectorFunctionEquiv)
    ((Equiv.prodCongr pointRandomnessSplit (Equiv.refl (GarblingFieldData × GarblingOracleData))).trans
      (Equiv.prodAssoc _ _ _))

/-- The source factors are independent under the actual uniform tape law. -/
theorem map_uniform_outputRowSourceEquiv [FieldCertificate] :
    (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map outputRowSourceEquiv =
      PMF.uniformOfFintype OutputRowSource := uniform_map_equiv outputRowSourceEquiv

theorem outputRowSourceEquiv_free [FieldCertificate]
    (sample : OffsetRandomness × GarblingOffsetRest) :
    (outputRowSourceEquiv sample).1 =
      (⟨sample.1.freeOffsets.toArray, by simpa using sample.1.freeOffsetCount⟩ : Vector Point 90) := by
  apply Vector.toList_inj.mp
  change (Vector.ofFn (offsetFunctionEquiv.symm sample.1)).toList = _
  rw [Vector.toList_ofFn]
  exact offsetFunctionEquiv_symm_list sample.1

/-- This view applies outputTargets to independent free points and scales. -/
def outputTargetView [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (output : Point) (sample : OutputRowSource) : Result × OutputRowRest :=
  (⟨input, outputTargets output sample.1 sample.2.1⟩, sample.2.2)

theorem simulatedOutputRowView_source [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (output : Point) (sample : OffsetRandomness × GarblingOffsetRest) :
    simulatedOutputRowView input output sample = outputTargetView input output (outputRowSourceEquiv sample) := by
  unfold simulatedOutputRowView outputTargetView
  rw [outputRowSourceEquiv_free]
  rfl

/-- The simulator target source has the exact independent product law. -/
theorem map_uniform_outputTargetView [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (output : Point) :
    (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map
      (simulatedOutputRowView input output) =
    (PMF.uniformOfFintype OutputRowSource).map (outputTargetView input output) := by
  conv_lhs => arg 1; ext sample; rw [simulatedOutputRowView_source]
  change (PMF.uniformOfFintype (OffsetRandomness × GarblingOffsetRest)).map
    (outputTargetView input output ∘ outputRowSourceEquiv) = _
  rw [← PMF.map_comp, map_uniform_outputRowSourceEquiv]

/-- Every later randomized observation preserves the output-row bound. -/
theorem actualOutputRowView_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Observation : Type*}
    (scalar : ScalarField) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) (witness : Garbling.Randomness) (parameter : Nat)
    (observe : Result × OutputRowRest → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype OutputRowSource).bind
        (observe ∘ outputTargetView input (scalarMultiplication scalar point))).toOuterMeasure event).toReal -
      (((randomTape witness parameter).bind
        (observe ∘ actualOutputRowView scalar input)).toOuterMeasure event).toReal|
        ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  rw [← PMF.bind_map (PMF.uniformOfFintype OutputRowSource)
      (outputTargetView input (scalarMultiplication scalar point)) observe,
    ← PMF.bind_map (randomTape witness parameter) (actualOutputRowView scalar input) observe,
    ← map_uniform_outputTargetView, ← map_uniform_mathematicalOutputRowView scalar input point,
    map_randomTape_actualOutputRowView scalar input point decoded, PMF.bind_map, PMF.bind_map]
  exact randomTape_point_observation_bound construction witness parameter
    (observe ∘ mathematicalOutputRowView scalar input point) event

end

end Kriterion.ArgoMAC.Security
