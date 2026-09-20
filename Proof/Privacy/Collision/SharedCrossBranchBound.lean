import Proof.Privacy.Collision.SharedBranchCollision
import Proof.Privacy.Source.ActualLabelSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048

/-- Each coordinate shares its label across these point range slots. The Y row
evaluates on the x-only cubic basis, so all three of its adaptors key on `x`. -/
def pointSharedSlotCount : EncPRF.Coordinate → Nat
  | .x => 12
  | .y => 12

/-- Each coordinate shares its label across these curve range slots. -/
def curveSharedSlotCount : EncPRF.Coordinate → Nat
  | .x => 6
  | .y => 4

/-- Each point family uses the coordinate that selects its actual branch. -/
def PointGateFamily.coordinate : PointGateFamily → EncPRF.Coordinate
  | .inl gate => if gate = 3 then .x else .y
  | .inr (.inl _) => .x
  | .inr (.inr gate) => if gate.val < 3 then .y else .x

/-- The coordinate grouping preserves the actual selected input bit. -/
theorem PointGateFamily.selectedBit_coordinate (family : PointGateFamily)
    (input : AffineInput) (position : Fin coordinateBitCount) :
    family.selectedBit input position = inputSelectedLabelBit input (family.coordinate, position) := by
  rcases family with gate | (gate | gate) <;> fin_cases gate <;> rfl

/-- The actual point families have twelve x slots and twelve y slots. -/
theorem pointSharedSlotCount_actual (coordinate : EncPRF.Coordinate) :
    Fintype.card ({family : PointGateFamily // family.coordinate = coordinate} × Fin 2) =
      pointSharedSlotCount coordinate := by
  cases coordinate <;> decide

/-- Each curve family uses the coordinate that selects its actual branch. -/
def curveSharedCoordinate (family : Fin 5) : EncPRF.Coordinate :=
  if family.val < 3 then .x else .y

/-- The actual curve families have six x slots and four y slots. -/
theorem curveSharedSlotCount_actual (coordinate : EncPRF.Coordinate) :
    Fintype.card ({family : Fin 5 // curveSharedCoordinate family = coordinate} × Fin 2) =
      curveSharedSlotCount coordinate := by
  cases coordinate <;> decide

/-- The point data retains every shared slot and all 91 digit tweaks. -/
structure SharedPointBranches (coordinate : EncPRF.Coordinate) where
  activeLabel : Block
  hiddenPad : Block
  tweak : Fin FieldMacToECMac.outputMacCount → Block
  activeOffset : Fin (pointSharedSlotCount coordinate) → Fin FieldMacToECMac.outputMacCount → Block
  hiddenOffset : Fin (pointSharedSlotCount coordinate) → Fin FieldMacToECMac.outputMacCount → Block

/-- The curve data retains every shared slot and its single tweak. -/
structure SharedCurveBranches (coordinate : EncPRF.Coordinate) where
  activeLabel : Block
  tweak : Fin 1 → Block
  activeOffset : Fin (curveSharedSlotCount coordinate) → Fin 1 → Block
  hiddenOffset : Fin (curveSharedSlotCount coordinate) → Fin 1 → Block

/-- This set expresses both exclusions in the original hidden source label. -/
def sharedCoordinateForbidden {coordinate : EncPRF.Coordinate}
    (point : SharedPointBranches coordinate) (curve : SharedCurveBranches coordinate) : Finset Block :=
  (sharedBranchForbidden point.activeLabel point.tweak point.activeOffset point.hiddenOffset).image
    (fun label => label ^^^ point.hiddenPad) ∪
  sharedBranchForbidden curve.activeLabel curve.tweak curve.activeOffset curve.hiddenOffset

/-- The bound counts each point and curve domain once for this coordinate. -/
theorem sharedCoordinateForbidden_card_le {coordinate : EncPRF.Coordinate}
    (point : SharedPointBranches coordinate) (curve : SharedCurveBranches coordinate) :
    (sharedCoordinateForbidden point curve).card ≤
      (pointSharedSlotCount coordinate + 1) * 91 ^ 2 + curveSharedSlotCount coordinate + 1 := by
  apply (Finset.card_union_le _ _).trans
  have pointBound := (Finset.card_image_le (s := sharedBranchForbidden point.activeLabel point.tweak point.activeOffset point.hiddenOffset) (f := fun label => label ^^^ point.hiddenPad)).trans
    (sharedBranchForbidden_card_le point.activeLabel point.tweak point.activeOffset point.hiddenOffset)
  have curveBound := sharedBranchForbidden_card_le curve.activeLabel curve.tweak
    curve.activeOffset curve.hiddenOffset
  simpa only [Fintype.card_fin, one_pow, Nat.mul_one, Nat.add_assoc] using
    Nat.add_le_add pointBound curveBound

/-- A retained source label avoids both linked point and curve collisions. -/
theorem sharedCoordinateForbidden_good {coordinate : EncPRF.Coordinate}
    (point : SharedPointBranches coordinate) (curve : SharedCurveBranches coordinate)
    (label : Block) (good : label ∉ sharedCoordinateForbidden point curve) :
    label ^^^ point.hiddenPad ∉ sharedBranchForbidden point.activeLabel point.tweak
      point.activeOffset point.hiddenOffset ∧
    label ∉ sharedBranchForbidden curve.activeLabel curve.tweak curve.activeOffset curve.hiddenOffset := by
  unfold sharedCoordinateForbidden at good
  constructor
  · intro member
    apply good
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨label ^^^ point.hiddenPad, member, by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]⟩
  · intro member
    exact good (Finset.mem_union_right _ member)

/-- This event includes all shared cross-branch collisions on the hidden tape. -/
def sharedCrossBranchCollision
    (point : (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (curve : (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1)
    (hidden : EncPRF.PermutationIndex → Block) : Prop :=
  ∃ index, hidden index ∈ sharedCoordinateForbidden (point index) (curve index)

private theorem uniform_label_eval [Fintype Block] (index : EncPRF.PermutationIndex) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map (fun hidden => hidden index) =
      PMF.uniformOfFintype Block := by
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween (Equiv.piSplitAt index (fun _ => Block)))
  simpa only [PMF.map_comp, map_uniform_prod_fst, Function.comp_def, Equiv.piSplitAt_apply] using law

/-- Each coordinate bound uses the exact uniform marginal of its source label. -/
theorem sharedCoordinateForbidden_mass_le [Fintype Block]
    (index : EncPRF.PermutationIndex)
    (point : SharedPointBranches index.1) (curve : SharedCurveBranches index.1) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).toOuterMeasure
      {hidden | hidden index ∈ sharedCoordinateForbidden point curve} ≤
      (((pointSharedSlotCount index.1 + 1) * 91 ^ 2 + curveSharedSlotCount index.1 + 1 : Nat) : ENNReal) /
        Fintype.card Block := by
  have marginal := uniform_label_eval index
  have mass := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure
    {label | label ∈ sharedCoordinateForbidden point curve}) marginal
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at mass
  rw [mass, PMF.toOuterMeasure_uniformOfFintype_apply]
  apply ENNReal.div_le_div_right
  exact_mod_cast (Fintype.card_of_subtype _ (fun _ => Iff.rfl)).trans_le
    (sharedCoordinateForbidden_card_le point curve)

/-- The 508 coordinate labels pay at most 54690772 inverse blocks. -/
theorem sharedCrossBranchCollision_mass_le [Fintype Block]
    (point : (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (curve : (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).toOuterMeasure
      {hidden | sharedCrossBranchCollision point curve hidden} ≤
      54690772 / (2 : ENNReal) ^ 128 := by
  have events : {hidden | sharedCrossBranchCollision point curve hidden} =
      ⋃ index, {hidden | hidden index ∈ sharedCoordinateForbidden (point index) (curve index)} := by
    ext hidden
    simp only [sharedCrossBranchCollision, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [events]
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply (Finset.sum_le_sum (fun index _ => sharedCoordinateForbidden_mass_le index
    (point index) (curve index))).trans
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have count : (∑ index : EncPRF.PermutationIndex,
      (((pointSharedSlotCount index.1 + 1) * 91 ^ 2 + curveSharedSlotCount index.1 + 1 : Nat) : ENNReal)) =
      54690772 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (Finset.univ : Finset EncPRF.Coordinate) = {.x, .y} from rfl,
      Finset.sum_pair (by decide)]
    change (254 * (((12 + 1) * 91 ^ 2 + 6 + 1 : Nat) : ENNReal) +
      254 * (((12 + 1) * 91 ^ 2 + 4 + 1 : Nat) : ENNReal)) = _
    norm_num
  rw [count, card, Nat.cast_pow, Nat.cast_ofNat]


/-- A prior can fix every offset before the uniform hidden labels are sampled. -/
theorem sharedCrossBranchCollision_prefix_mass_le [Fintype Block] {Prefix : Type*}
    (prefixLaw : PMF Prefix)
    (point : Prefix → (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (curve : Prefix → (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1) :
    (prefixLaw.bind fun prior =>
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map fun hidden =>
        (prior, hidden)).toOuterMeasure
      {sample | sharedCrossBranchCollision (point sample.1) (curve sample.1) sample.2} ≤
      54690772 / (2 : ENNReal) ^ 128 := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' prior, prefixLaw prior * (54690772 / (2 : ENNReal) ^ 128) := by
      apply ENNReal.tsum_le_tsum
      intro prior
      apply mul_le_mul_right
      rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
      exact sharedCrossBranchCollision_mass_le (point prior) (curve prior)
    _ = _ := by rw [ENNReal.tsum_mul_right, prefixLaw.tsum_coe, one_mul]

private instance sharedCrossInputMacKeyFinite : Fintype InputMacKey := publicInputMacKeyFintype
private instance sharedCrossInputMacKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual key split permits offsets that depend on every selected public label. -/
theorem sharedCrossBranchCollision_selectedKey_mass_le [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool)
    (point : (EncPRF.PermutationIndex → Block) →
      (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (curve : (EncPRF.PermutationIndex → Block) →
      (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedCrossBranchCollision (point ((selectedKeyLabelsEquiv selected key).1))
        (curve ((selectedKeyLabelsEquiv selected key).1)) ((selectedKeyLabelsEquiv selected key).2)} ≤
      54690772 / (2 : ENNReal) ^ 128 := by
  have bound := sharedCrossBranchCollision_prefix_mass_le
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) point curve
  have productLaw : PMF.uniformOfFintype
      ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block)) =
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).bind fun active =>
        (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map fun hidden => (active, hidden) := by
    calc
      _ = (PMF.uniformOfFintype
          ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))).map Prod.swap :=
        (map_uniformOfFintype_equivBetween (Equiv.prodComm _ _)).symm
      _ = _ := by
        rw [uniform_prod_eq_bind, PMF.map_bind]
        simp_rw [PMF.map_comp]
        rfl
  rw [← productLaw, ← map_uniform_selectedKeyLabels selected,
    PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at bound
  exact bound


private instance sharedCrossHiddenGateFinite (gates : Nat) : Fintype (HiddenGateSample gates) := inferInstance
private instance sharedCrossHiddenRowFinite : Fintype HiddenRowSample := inferInstance

/-- This source samples the row data before its independent hidden labels. -/
def sharedBranchSource [Fintype Block] : PMF
    ((Fin FieldMacToECMac.outputMacCount → HiddenRowSample) × (EncPRF.PermutationIndex → Block)) :=
  (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)).bind fun hiddenRows =>
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map fun labels => (hiddenRows, labels)

/-- The source retains the exact row distribution. -/
theorem sharedBranchSource_rows [Fintype Block] : sharedBranchSource.map Prod.fst =
    PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample) := by
  simp only [sharedBranchSource, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)).bind
    (fun row => (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map
      (Function.const _ row)) = _
  simp only [PMF.map_const, PMF.bind_pure]

/-- The combined branch bound permits every offset to depend on the row data. -/
theorem sharedBranchSource_collision_mass_le [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue)
    (point : (Fin FieldMacToECMac.outputMacCount → HiddenRowSample) →
      (index : EncPRF.PermutationIndex) → SharedPointBranches index.1)
    (curve : (Fin FieldMacToECMac.outputMacCount → HiddenRowSample) →
      (index : EncPRF.PermutationIndex) → SharedCurveBranches index.1) :
    sharedBranchSource.toOuterMeasure
      {sample | pointBranchCollision visible rows input targets sample.1 ∨
        sharedCrossBranchCollision (point sample.1) (curve sample.1) sample.2} ≤
      (242713777716 / 1000) / (2 : ENNReal) ^ 128 := by
  have first := pointBranchCollision_mass_le_tight visible rows input targets
  rw [← sharedBranchSource_rows, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at first
  have second := sharedCrossBranchCollision_prefix_mass_le
    (PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample)) point curve
  have unionBound := MeasureTheory.measure_union_le (μ := sharedBranchSource.toOuterMeasure)
    {sample | pointBranchCollision visible rows input targets sample.1}
    {sample | sharedCrossBranchCollision (point sample.1) (curve sample.1) sample.2}
  apply unionBound.trans
  apply (add_le_add first second).trans
  simp only [div_eq_mul_inv, ← add_mul]
  apply mul_le_mul_left
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

end
end Kriterion.ArgoMAC.Security
