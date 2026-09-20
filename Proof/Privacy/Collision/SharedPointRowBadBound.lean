import Proof.Privacy.Collision.SharedCrossBranchBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The full hidden source pays only the point-row term before the shared label ratio. -/
theorem sharedPointBranchCollision_fullTape_mass_le [Fintype Block]
    (visible : Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : AffineInput)
    (targets : Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue) :
    (PMF.uniformOfFintype HiddenPublicSample).toOuterMeasure
      {hidden | pointBranchCollision visible rows input targets hidden.2} ≤
      (169786660680 / 1000) / (2 : ENNReal) ^ 128 := by
  have marginal : (PMF.uniformOfFintype HiddenPublicSample).map Prod.snd =
      PMF.uniformOfFintype (Fin FieldMacToECMac.outputMacCount → HiddenRowSample) :=
    map_uniform_prod_snd
  have bound := pointBranchCollision_mass_le_tight visible rows input targets
  rw [← marginal, PMF.toOuterMeasure_map_apply] at bound
  exact bound

/-- An adaptive prefix keeps the tight row bound when it precedes the hidden source draw. -/
theorem sharedPointBranchCollision_prefix_mass_le [Fintype Block] {Prior : Type*}
    (prefixLaw : PMF Prior)
    (visible : Prior → Fin FieldMacToECMac.outputMacCount → VisibleRowSample)
    (rows : Prior → Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (input : Prior → AffineInput)
    (targets : Prior → Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue) :
    (prefixLaw.bind fun prior => (PMF.uniformOfFintype HiddenPublicSample).map (Prod.mk prior)).toOuterMeasure
      {sample | pointBranchCollision (visible sample.1) (rows sample.1) (input sample.1)
        (targets sample.1) sample.2.2} ≤
      (169786660680 / 1000) / (2 : ENNReal) ^ 128 := by
  apply Probability.bind_event_le
  intro prior _
  rw [PMF.toOuterMeasure_map_apply]
  exact sharedPointBranchCollision_fullTape_mass_le (visible prior) (rows prior) (input prior) (targets prior)

end
end Kriterion.ArgoMAC.Security
