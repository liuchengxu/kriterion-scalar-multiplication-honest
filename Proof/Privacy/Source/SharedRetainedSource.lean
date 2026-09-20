import Proof.Privacy.Collision.SharedCurveAssignments

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048

/-- This context fixes the visible source and the selected input before hidden sampling. -/
structure Context where
  visible : VisiblePublicSample
  mask : BaseField
  rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows
  input : AffineInput
  curveTarget : BaseField
  targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue
  activeCurveLabels : EncPRF.PermutationIndex → Block
  activePointLabels : EncPRF.PermutationIndex → Block
  hiddenPointPads : EncPRF.PermutationIndex → Block

/-- The source reconstructs all actual mask equations from the visible and hidden data. -/
def Context.source (context : Context) (hidden : HiddenPublicSample) : CircuitMaskSample :=
  reconstructedCircuitSource (PublicSample.visibleHiddenEquiv.symm (context.visible, hidden))
    context.mask context.rows context.input context.curveTarget context.targets

/-- The source retains the full good hash lift at every actual gate. -/
def Context.lifts (context : Context) (hidden : HiddenPublicSample) : RawCircuitGate → FullHashLift :=
  fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv (context.source hidden)).1 gate)

/-- The point data uses the actual reconstructed row offsets. -/
def Context.pointBranches (context : Context) (hidden : HiddenPublicSample)
    (index : EncPRF.PermutationIndex) : SharedPointBranches index.1 :=
  pointSharedBranches context.visible.2 context.rows context.input context.targets hidden.2
    context.activePointLabels context.hiddenPointPads index

/-- The curve data uses the actual reconstructed circuit source. -/
def Context.curveBranches (context : Context) (hidden : HiddenPublicSample)
    (index : EncPRF.PermutationIndex) : SharedCurveBranches index.1 :=
  curveSharedBranches (context.source hidden) (context.lifts hidden) context.input
    context.activeCurveLabels index

/-- This event covers repeated row offsets and shared cross-branch assignments. -/
def Context.collision (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block)) : Prop :=
  pointBranchCollision context.visible.2 context.rows context.input context.targets sample.1.2 ∨
    sharedCrossBranchCollision (context.pointBranches sample.1) (context.curveBranches sample.1) sample.2

private instance hiddenGateFinite (gates : Nat) : Fintype (HiddenGateSample gates) := inferInstance
private instance hiddenRowFinite : Fintype HiddenRowSample := inferInstance
private instance hiddenPublicFinite : Fintype HiddenPublicSample := inferInstance

/-- This source samples every hidden target before its independent unused labels. -/
def law [Fintype Block] : PMF (HiddenPublicSample × (EncPRF.PermutationIndex → Block)) :=
  (PMF.uniformOfFintype HiddenPublicSample).bind fun hidden =>
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map fun labels => (hidden, labels)

/-- The added unused labels preserve the exact hidden target distribution. -/
theorem law_targets [Fintype Block] : law.map Prod.fst = PMF.uniformOfFintype HiddenPublicSample := by
  simp only [law, PMF.map_bind, PMF.map_comp, Function.comp_def]
  change (PMF.uniformOfFintype HiddenPublicSample).bind
    (fun hidden => (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map
      (Function.const _ hidden)) = _
  simp only [PMF.map_const, PMF.bind_pure]

/-- The source also preserves the exact independent row marginal. -/
theorem law_rows [Fintype Block] : law.map (fun sample => sample.1.2) =
    PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample) := by
  have result := congrArg (fun distribution => distribution.map Prod.snd) law_targets
  rw [PMF.map_comp, map_uniform_prod_snd] at result
  exact result

/-- This bound uses the actual reconstructed source for both point and curve assignments. -/
theorem collision_mass_le [Fintype Block] (context : Context) :
    law.toOuterMeasure {sample | context.collision sample} ≤
      (248222021716 / 1000) / (2 : ENNReal) ^ 128 := by
  have first := pointBranchCollision_mass_le_tight context.visible.2 context.rows context.input context.targets
  rw [← law_rows, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at first
  have second := sharedCrossBranchCollision_prefix_mass_le
    (PMF.uniformOfFintype HiddenPublicSample) context.pointBranches context.curveBranches
  apply (MeasureTheory.measure_union_le (μ := law.toOuterMeasure)
    {sample | pointBranchCollision context.visible.2 context.rows context.input context.targets sample.1.2}
    {sample | sharedCrossBranchCollision (context.pointBranches sample.1)
      (context.curveBranches sample.1) sample.2}).trans
  apply (add_le_add first second).trans
  simp only [div_eq_mul_inv, ← add_mul]
  apply mul_le_mul_left
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

/-- A good source supplies the injective point assignments for every shared slot. -/
theorem point_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (index : EncPRF.PermutationIndex)
    (slot : Fin (pointSharedSlotCount index.1)) :
    let branches := context.pointBranches sample.1 index
    Function.Injective (Sum.elim
      (fun row => (sample.2 index ^^^ context.hiddenPointPads index) ^^^ branches.tweak row)
      (fun row => context.activePointLabels index ^^^ branches.tweak row)) ∧
    Function.Injective (Sum.elim
      (fun row => branches.hiddenOffset slot row ^^^ (sample.2 index ^^^ context.hiddenPointPads index))
      (fun row => branches.activeOffset slot row ^^^ context.activePointLabels index)) := by
  exact pointSharedBranches_assignments_injective context.visible.2 context.rows context.input
    context.targets sample.1.2 context.activePointLabels context.hiddenPointPads
    (context.curveBranches sample.1) sample.2 (fun event => good (Or.inl event))
    (fun event => good (Or.inr event)) index slot

/-- A good source supplies the injective curve assignments for every shared slot. -/
theorem curve_assignments_injective (context : Context)
    (sample : HiddenPublicSample × (EncPRF.PermutationIndex → Block))
    (good : ¬ context.collision sample) (index : EncPRF.PermutationIndex)
    (slot : Fin (curveSharedSlotCount index.1)) :
    let branches := context.curveBranches sample.1 index
    Function.Injective (Sum.elim
      (fun row => sample.2 index ^^^ branches.tweak row)
      (fun row => context.activeCurveLabels index ^^^ branches.tweak row)) ∧
    Function.Injective (Sum.elim
      (fun row => branches.hiddenOffset slot row ^^^ sample.2 index)
      (fun row => branches.activeOffset slot row ^^^ context.activeCurveLabels index)) := by
  exact curveSharedBranches_assignments_injective (context.source sample.1) (context.lifts sample.1)
    context.input context.activeCurveLabels (context.pointBranches sample.1) sample.2
    (fun event => good (Or.inr event)) index slot

/-- Each point offset in the retained context equals its actual raw-source offset. -/
theorem point_source_offset (context : Context) (hidden : HiddenPublicSample)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    circuitSourceOffset (context.source hidden) (context.lifts hidden) (pointRawGate row family position) slot ^^^
        (rawCircuitLocation (pointRawGate row family position)).tweak =
      pointBranchOffset row (context.visible.2 row) (hidden.2 row) (context.rows row)
        context.input (context.targets row) family position slot := by
  unfold Context.lifts
  simp only [Context.source]
  rw [reconstructedCircuitSource_pointOffset]
  simp only [PublicSample.visibleHiddenEquiv, Equiv.coe_fn_symm_mk, Vector.get_ofFn,
    Equiv.apply_symm_apply]
  rcases family with gate | (gate | gate) <;> rfl

end
end Kriterion.ArgoMAC.Security.SharedRetained
