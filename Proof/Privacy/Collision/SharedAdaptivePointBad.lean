import Proof.Privacy.Collision.SharedAdaptiveHidden

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype publicVectorFintype ciphertextFintype
  bitAdaptorTableFintype publicBitAdaptorKeyFintype
local instance pointBadKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance pointBadVisibleNonempty : Nonempty VisiblePublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).1⟩
local instance pointBadHiddenNonempty : Nonempty HiddenPublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).2⟩
local instance pointBadOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

abbrev SharedVisiblePrefixState (State : Type*) := VisiblePublicSample × SharedLabelPrefixState State

/-- This operation adds the independent hidden targets to the retained shared prefix. -/
def sharedPrefixWithHidden {State : Type*} (prior : SharedVisiblePrefixState State)
    (hidden : HiddenPublicSample) : SharedLabelPrefixState State :=
  let sample := PublicSample.visibleHiddenEquiv.symm (prior.1, hidden)
  (prior.2.1, prior.2.2.1,
    {prior.2.2.2.1 with curve := sample.curveRequest, points := sample.pointRequests}, prior.2.2.2.2)

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)

/-- This law retains the actual shared prefix before it draws the hidden targets. -/
def sharedIdealVisiblePrefix : PMF (SharedVisiblePrefixState adversary.State) :=
  (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracles =>
    (PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype InputMacKey).bind fun key =>
        (PMF.uniformOfFintype VisiblePublicSample).bind fun visible =>
          let base := Shared.Simulator.initialState
            (PublicSample.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample), key, bridge) oracles
          (runOracleProgramWithTranscript idealOracleHandler
            (adversary.chooseInput parameter base.table auxiliary) base.oracle).map fun selected =>
              (visible, base.table, selected.1, {base with oracle := selected.2.1}, selected.2.2)

/-- The retained prefix and independent targets give the exact actual shared prefix. -/
theorem sharedIdealVisiblePrefix_hidden :
    (sharedIdealVisiblePrefix adversary parameter auxiliary).bind
        (fun prior => (PMF.uniformOfFintype HiddenPublicSample).map (sharedPrefixWithHidden prior)) =
      sharedIdealCircuitPrefix adversary parameter scalar auxiliary := by
  rw [sharedIdealCircuitPrefix_hidden]
  simp only [sharedIdealVisiblePrefix, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

/-- The point-row flag uses source rows and targets chosen before the hidden target draw. -/
def sharedIdealPointBranchCollisionFlag {Extra : Type*}
    (extra : SharedVisiblePrefixState adversary.State → PMF Extra)
    (rows : SharedVisiblePrefixState adversary.State → Extra →
      Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (targets : SharedVisiblePrefixState adversary.State → Extra →
      Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue) : PMF Bool :=
  (sharedIdealVisiblePrefix adversary parameter auxiliary).bind fun prior =>
    (extra prior).bind fun selected =>
      (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
        @decide (pointBranchCollision prior.1.2 (rows prior selected) prior.2.2.1.1
          (targets prior selected) hidden.2) (Classical.propDecidable _)

/-- The actual shared prefix retains the tight point-row collision loss. -/
theorem sharedIdealPointBranchCollisionFlag_mass_le [Fintype Block] {Extra : Type*}
    (extra : SharedVisiblePrefixState adversary.State → PMF Extra)
    (rows : SharedVisiblePrefixState adversary.State → Extra →
      Fin FieldMacToECMac.outputMacCount → Coordinates.Rows)
    (targets : SharedVisiblePrefixState adversary.State → Extra →
      Fin FieldMacToECMac.outputMacCount → FieldMacToECMac.HomogeneousValue) :
    (sharedIdealPointBranchCollisionFlag adversary parameter auxiliary extra rows targets).toOuterMeasure
      {flag | flag = true} ≤ (169786660680 / 1000) / (2 : ENNReal) ^ 128 := by
  unfold sharedIdealPointBranchCollisionFlag
  apply Probability.bind_event_le
  intro prior _
  apply Probability.bind_event_le
  intro selected _
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  simp only [decide_eq_true_eq]
  exact sharedPointBranchCollision_fullTape_mass_le prior.1.2 (rows prior selected)
    prior.2.2.1.1 (targets prior selected)

end
end Kriterion.ArgoMAC.Security
