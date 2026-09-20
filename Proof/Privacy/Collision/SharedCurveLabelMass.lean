import Proof.Privacy.Collision.SharedCurveHiddenLabels

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
open scoped ENNReal
noncomputable section
local instance curveLabelMassKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveLabelMassKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The hidden point-label average retains the same cross-branch exclusion bound. -/
theorem curveHidden_cross_mass_le [Fintype Block] (context : Context) (hidden : HiddenPublicSample) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
        ((context.curveHidden key).curveBranches hidden) (curveUnused key)} ≤
      54690772 / (2 : ENNReal) ^ 128 := by
  have bound := sharedCrossBranchCollision_prefix_mass_le
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block))
    (fun labels => ({context with activePointLabels := labels}).pointBranches hidden)
    (fun labels => ({context with activePointLabels := labels}).curveBranches hidden)
  have pairLaw : PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block)) =
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).bind fun first =>
        (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map fun second => (first, second) := by
    calc
      _ = (PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))).map Prod.swap :=
        (map_uniformOfFintype_equivBetween (Equiv.prodComm _ _)).symm
      _ = _ := by
        rw [uniform_prod_eq_bind, PMF.map_bind]
        simp_rw [PMF.map_comp]
        rfl
  rw [← pairLaw, ← map_uniform_selectedKeyLabels (fun _ => true),
    PMF.toOuterMeasure_map_apply] at bound
  exact bound

/-- Both hidden arrays pay each cross-branch or post-query exclusion once. -/
theorem curveHidden_failure_mass_le [Fintype Block] (context : Context) (hidden : HiddenPublicSample)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
          ((context.curveHidden key).curveBranches hidden) (curveUnused key) ∨
        sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key} ≤
      (54690772 + (364 * history.length : Nat)) / (2 : ENNReal) ^ 128 := by
  have crossing := curveHidden_cross_mass_le context hidden
  have queries := curveHiddenQuery_mass_le context hidden history
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card, Nat.cast_pow, Nat.cast_ofNat] at queries
  apply (MeasureTheory.measure_union_le
    (μ := (PMF.uniformOfFintype InputMacKey).toOuterMeasure)
    {key | sharedCrossBranchCollision ((context.curveHidden key).pointBranches hidden)
      ((context.curveHidden key).curveBranches hidden) (curveUnused key)}
    {key | sharedPrequeryLabelCollision history (curveHiddenQueryUses context hidden history) key}).trans
  exact (add_le_add crossing queries).trans_eq (ENNReal.add_div ..).symm

end
end Kriterion.ArgoMAC.Security.SharedRetained
