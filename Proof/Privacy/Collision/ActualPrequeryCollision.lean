import Proof.Privacy.Collision.AdaptiveBadBound
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype
local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The initial oracle excludes both hidden label and bridge keys. -/
theorem initialSimulatorOracle_keys (coin : SimulatorCoin) (key : InputMacKey) (bridge : BaseField) :
    ({coin with inputKey := key, bridgeKey := bridge} : SimulatorCoin).state.oracle =
      coin.state.oracle := rfl

/-- The public table excludes both hidden label and bridge keys. -/
theorem initialSimulatorTable_keys (coin : SimulatorCoin) (key : InputMacKey) (bridge : BaseField) :
    ({coin with inputKey := key, bridgeKey := bridge} : SimulatorCoin).state.table =
      coin.state.table := rfl

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The actual prefix keeps every answer and query record. -/
def actualCoinPrefix (coin : SimulatorCoin) :=
  runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter coin.state.table auxiliary) coin.state.oracle

/-- The actual input choice and complete prefix exclude both hidden keys. -/
theorem actualCoinPrefix_keys (coin : SimulatorCoin) (key : InputMacKey) (bridge : BaseField) :
    actualCoinPrefix adversary parameter auxiliary {coin with inputKey := key, bridgeKey := bridge} =
      actualCoinPrefix adversary parameter auxiliary coin := rfl

/-- The source kernel receives every prefix field except the hidden label key. -/
abbrev ActualPrefixSourceKernel := PublicSample → SimulatorOracleCoin → BaseField →
  (AffineInput × adversary.State) → SimulatorState →
    List (Sigma Garbling.oracleSpec.Answer) → PMF CircuitMaskSample

/-- This flag tests the actual adaptive prefix against the reconstructed source. -/
def actualSourcePrequeryFlag (source : ActualPrefixSourceKernel adversary) : PMF Bool :=
  (PMF.uniformOfFintype SimulatorCoin).bind fun coin =>
    (actualCoinPrefix adversary parameter auxiliary coin).bind fun selected =>
      (source coin.tableSample coin.oracles coin.bridgeKey selected.1 selected.2.1 selected.2.2).map fun sample =>
        @decide (prequeryLabelCollision (fixedOracleTranscriptRecords selected.2.2)
          (sourcePrequeryLabelUses coin.oracles coin.bridgeKey sample
            (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv sample).1 gate))
            (fixedOracleTranscriptRecords selected.2.2)) coin.inputKey) (Classical.propDecidable _)

/-- The actual prefix permits independent label resampling after the source choice. -/
theorem actualSourcePrequeryFlag_resample (source : ActualPrefixSourceKernel adversary) :
    actualSourcePrequeryFlag adversary parameter auxiliary source =
      (PMF.uniformOfFintype SimulatorCoin).bind fun coin =>
        (actualCoinPrefix adversary parameter auxiliary coin).bind fun selected =>
          (source coin.tableSample coin.oracles coin.bridgeKey selected.1 selected.2.1 selected.2.2).bind fun sample =>
            (PMF.uniformOfFintype InputMacKey).map fun key =>
              @decide (prequeryLabelCollision (fixedOracleTranscriptRecords selected.2.2)
                (sourcePrequeryLabelUses coin.oracles coin.bridgeKey sample
                  (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv sample).1 gate))
                  (fixedOracleTranscriptRecords selected.2.2)) key) (Classical.propDecidable _) := by
  unfold actualSourcePrequeryFlag
  conv_lhs => rw [uniform_simulatorCoin_rekey]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype SimulatorCoin).bind
  funext coin
  change (PMF.uniformOfFintype InputMacKey).bind (fun key =>
    (actualCoinPrefix adversary parameter auxiliary coin).bind (fun selected =>
      (source coin.tableSample coin.oracles coin.bridgeKey selected.1 selected.2.1 selected.2.2).map (fun sample =>
        @decide (prequeryLabelCollision (fixedOracleTranscriptRecords selected.2.2)
          (sourcePrequeryLabelUses coin.oracles coin.bridgeKey sample
            (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv sample).1 gate))
            (fixedOracleTranscriptRecords selected.2.2)) key) (Classical.propDecidable _)))) = _
  rw [PMF.bind_comm]
  apply congrArg (actualCoinPrefix adversary parameter auxiliary coin).bind
  funext selected
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

/-- The actual adaptive source pays the full prequery loss once. -/
theorem actualSourcePrequeryFlag_mass_le [Fintype Block]
    (source : ActualPrefixSourceKernel adversary) :
    (actualSourcePrequeryFlag adversary parameter auxiliary source).toOuterMeasure {flag | flag = true} ≤
      (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  rw [actualSourcePrequeryFlag_resample]
  apply Probability.bind_event_le
  intro coin _
  apply Probability.bind_event_le
  intro selected member
  apply Probability.bind_event_le
  intro sample _
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  simp only [decide_eq_true_eq]
  apply (sourcePrequeryLabelCollision_mass_le coin.oracles coin.bridgeKey sample _
    (fixedOracleTranscriptRecords selected.2.2)).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 182 ((fixedOracleTranscriptRecords_length_le selected.2.2).trans
    (runOracleProgramWithTranscript_length_le _ _ _ _ member))

end
end Kriterion.ArgoMAC.Security
