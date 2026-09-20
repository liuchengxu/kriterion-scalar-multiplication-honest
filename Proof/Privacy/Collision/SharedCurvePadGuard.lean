import Proof.Privacy.Collision.SharedCurveLabelMass
import Proof.Privacy.Collision.PadRestrictedCount

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
open scoped ENNReal
noncomputable section
local instance curveGuardKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveGuardKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This event excludes equal selected and unused linking pads. -/
def curveHiddenPadBad (context : Context) (key : InputMacKey) : Prop :=
  ∃ index, inputKeyLabel key index true = context.activeCurveLabels index ^^^ context.hiddenPointPads index

/-- The two hidden arrays pay at most one inverse block per coordinate for the pad guard. -/
theorem curveHiddenPadBad_mass_le [Fintype Block] (context : Context) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure {key | curveHiddenPadBad context key} ≤
      508 / (Fintype.card Block : ENNReal) := by
  classical
  rw [show {key | curveHiddenPadBad context key} =
      ⋃ index, {key | inputKeyLabel key index true = context.activeCurveLabels index ^^^ context.hiddenPointPads index} by
    ext key
    simp only [curveHiddenPadBad, Set.mem_setOf_eq, Set.mem_iUnion]]
  apply (MeasureTheory.measure_iUnion_le _).trans
  have mass (index : EncPRF.PermutationIndex) :
      (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | inputKeyLabel key index true = context.activeCurveLabels index ^^^ context.hiddenPointPads index} =
          (Fintype.card Block : ENNReal)⁻¹ := by
    have law := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure
      {context.activeCurveLabels index ^^^ context.hiddenPointPads index}) (uniform_inputKeyLabel index true)
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] at law
    exact law
  simp_rw [mass]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have count : Fintype.card EncPRF.PermutationIndex = 508 := by
    have coordinate : Fintype.card EncPRF.Coordinate = 2 := by decide
    norm_num [EncPRF.PermutationIndex, coordinateBitCount, Fintype.card_prod, Fintype.card_fin, coordinate]
  rw [count, div_eq_mul_inv]
  norm_num

/-- The curve-only source pays the pad guard and query exclusions in one relative loss. -/
theorem curveHidden_guard_failure_mass_le [Fintype Block] (context : Context) (hidden : HiddenPublicSample)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | (sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
          ((context.curveHidden key).curveBranches hidden) (curveUnused key) ∨
        sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key) ∨
          curveHiddenPadBad context key} ≤
      (54691280 + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128 := by
  have retained := curveHidden_failure_mass_le context hidden history
  have guard := curveHiddenPadBad_mass_le context
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card, Nat.cast_pow, Nat.cast_ofNat] at guard
  apply (MeasureTheory.measure_union_le
    (μ := (PMF.uniformOfFintype InputMacKey).toOuterMeasure)
    {key | sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
        ((context.curveHidden key).curveBranches hidden) (curveUnused key) ∨
      sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key}
    {key | curveHiddenPadBad context key}).trans
  apply (add_le_add retained guard).trans
  rw [← ENNReal.add_div]
  apply ENNReal.div_le_div_right
  norm_num
  exact le_of_eq (by ring)

end
end Kriterion.ArgoMAC.Security.SharedRetained
