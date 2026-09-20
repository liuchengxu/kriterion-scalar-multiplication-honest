import Proof.Privacy.Collision.SharedAdaptivePrequery
import Proof.Privacy.Collision.SharedPointRowBadBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype publicVectorFintype ciphertextFintype
  bitAdaptorTableFintype publicBitAdaptorKeyFintype
local instance sharedHiddenKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance sharedHiddenSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance sharedHiddenVisibleNonempty : Nonempty VisiblePublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).1⟩
local instance sharedHiddenTargetNonempty : Nonempty HiddenPublicSample :=
  ⟨(PublicSample.visibleHiddenEquiv defaultSimulatorCoin.tableSample).2⟩
local instance sharedHiddenOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

/-- The public sample separates its table data from its hidden targets. -/
theorem sharedPublicSample_visible_hidden :
    PMF.uniformOfFintype PublicSample =
      (PMF.uniformOfFintype VisiblePublicSample).bind fun visible =>
        (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
          PublicSample.visibleHiddenEquiv.symm (visible, hidden) := by
  calc
    _ = (PMF.uniformOfFintype (VisiblePublicSample × HiddenPublicSample)).map
        PublicSample.visibleHiddenEquiv.symm :=
      (map_uniformOfFintype_equivBetween PublicSample.visibleHiddenEquiv.symm).symm
    _ = (PMF.uniformOfFintype HiddenPublicSample).bind fun hidden =>
        (PMF.uniformOfFintype VisiblePublicSample).map fun visible =>
          PublicSample.visibleHiddenEquiv.symm (visible, hidden) := by
      rw [uniform_prod_eq_bind, PMF.map_bind]
      simp only [PMF.map_comp, Function.comp_def]
    _ = _ := by
      simp only [PMF.map, Function.comp_def]
      exact PMF.bind_comm _ _ _

/-- Hidden targets do not change the shared public table. -/
theorem sharedInitialState_hidden_table (visible : VisiblePublicSample)
    (first second : HiddenPublicSample) (key : InputMacKey) (bridge : BaseField)
    (oracles : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (Shared.Simulator.initialState (PublicSample.visibleHiddenEquiv.symm (visible, first), key, bridge) oracles).table =
      (Shared.Simulator.initialState (PublicSample.visibleHiddenEquiv.symm (visible, second), key, bridge) oracles).table :=
  simulatorCoin_hidden_table (visible, defaultSimulatorCoin.oracles, key, bridge) first second

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)

/-- The shared adaptive prefix precedes the hidden target draw. -/
theorem sharedIdealCircuitPrefix_hidden :
    sharedIdealCircuitPrefix adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracles =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype InputMacKey).bind fun key =>
            (PMF.uniformOfFintype VisiblePublicSample).bind fun visible =>
              let base := Shared.Simulator.initialState
                (PublicSample.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample), key, bridge) oracles
              (runOracleProgramWithTranscript idealOracleHandler
                (adversary.chooseInput parameter base.table auxiliary) base.oracle).bind fun selected =>
                  (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
                    (base.table, selected.1,
                      {Shared.Simulator.initialState
                        (PublicSample.visibleHiddenEquiv.symm (visible, hidden), key, bridge) oracles with
                          oracle := selected.2.1}, selected.2.2) := by
  unfold sharedIdealCircuitPrefix
  rw [sharedTape_bind]
  simp only [sharedRunCircuitSimulatorWithTranscript, PMF.map_comp, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind)
  funext oracles
  apply congrArg ((PMF.uniformOfFintype BaseField).bind)
  funext bridge
  apply congrArg ((PMF.uniformOfFintype InputMacKey).bind)
  funext key
  rw [sharedPublicSample_visible_hidden, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype VisiblePublicSample).bind)
  funext visible
  simp_rw [sharedInitialState_hidden_table visible _ (Classical.arbitrary HiddenPublicSample)]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

end
end Kriterion.ArgoMAC.Security
