import Proof.Privacy.Collision.SharedRetainedFlags

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype
local instance retainedDistributionKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance retainedDistributionSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance retainedDistributionOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩
attribute [local irreducible] PMF.uniformOfFintype sharedRetainedCoinPrefix

variable {Aux : Type*}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The offline coin retains its own input key in both source flags. -/
def sharedRetainedCoinFlags (rows : Rows) (mask : BaseField)
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (coin : SimulatorSampling.OfflineCoin) : PMF (Bool × Bool) :=
  (sharedRetainedCoinPrefix adversary parameter auxiliary oracle coin.2.2 coin.1).map fun selected =>
    let source := (circuitMaskSampleSplit coin.2.2 mask rows selected.1.1 coin.1).2
    let history := sharedFixedTranscriptRecords selected.2.2
    (@decide (retainedSourceBirthday coin.1 rows selected.1.1) (Classical.propDecidable _),
      @decide (sharedPrequeryLabelCollision history
        (sharedSourcePrequeryUses ⟨Shared.expandOracle oracle.1, oracle.2.1, oracle.2.2⟩ coin.2.2 source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) history) coin.2.1)
        (Classical.propDecidable _))

/-- The actual offline coin order gives the same shared source flags. -/
theorem sharedRetainedFlags_offline (rows : Rows) (mask : BaseField) :
    (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
      (fun oracle => (PMF.uniformOfFintype SimulatorSampling.OfflineCoin).bind
        (sharedRetainedCoinFlags adversary parameter auxiliary rows mask oracle)) =
      sharedRetainedFlags adversary parameter auxiliary rows mask := by
  unfold sharedRetainedFlags
  apply congrArg (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
  funext oracle
  rw [uniform_prod_eq_bind, uniform_prod_eq_bind]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype BaseField).bind
  funext bridge
  rw [PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype PublicSample).bind
  funext sample
  simp only [sharedRetainedCoinFlags, sharedRetainedFlagsAt, PMF.map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- The actual offline source has the joint point-row and prefix bound. -/
theorem sharedRetainedCoinFlags_mass_le (rows : Rows) (mask : BaseField) :
    ((PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
      (fun oracle => (PMF.uniformOfFintype SimulatorSampling.OfflineCoin).bind
        (sharedRetainedCoinFlags adversary parameter auxiliary rows mask oracle))).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        (169786660680 / 1000) / (2 : ENNReal) ^ 128 +
          (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  rw [sharedRetainedFlags_offline]
  exact sharedRetainedFlags_mass_le adversary parameter auxiliary rows mask

end
end Kriterion.ArgoMAC.Security
