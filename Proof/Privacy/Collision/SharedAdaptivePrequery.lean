import Proof.Privacy.Collision.SharedPrequeryBound
import Proof.Privacy.Simulator.SharedGameDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype
local instance sharedAdaptiveKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance sharedAdaptiveSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance sharedAdaptiveOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

abbrev SharedLabelPrefixState (State : Type*) :=
  Pipeline.Table × (AffineInput × State) × Shared.Simulator.State ×
    List (Sigma sharedRealOracleSpec.Answer)

def sharedRekeyPrefix {State : Type*} (prior : SharedLabelPrefixState State) (key : InputMacKey) :
    SharedLabelPrefixState State :=
  (prior.1, prior.2.1, {prior.2.2.1 with inputKey := key}, prior.2.2.2)

def sharedErasePrefixKey {State : Type*} (prior : SharedLabelPrefixState State) : SharedLabelPrefixState State :=
  sharedRekeyPrefix prior defaultSimulatorCoin.inputKey

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)

/-- The shared prefix retains the private frame and the actual public transcript. -/
def sharedIdealCircuitPrefix : PMF (SharedLabelPrefixState adversary.State) :=
  (Shared.Simulator.tape parameter (Garbling.topology scalar)).bind fun state =>
    (runOracleProgramWithTranscript circuitSimulatorOracleHandler
      (adversary.chooseInput parameter state.table auxiliary) state).map
        (fun selected => (state.table, selected))

/-- The shared prefix samples its unused input key after every public query. -/
theorem sharedIdealCircuitPrefix_key :
    sharedIdealCircuitPrefix adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracles =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype PublicSample).bind fun sample =>
            let base := Shared.Simulator.initialState (sample, defaultSimulatorCoin.inputKey, bridge) oracles
            (runOracleProgramWithTranscript idealOracleHandler
              (adversary.chooseInput parameter base.table auxiliary) base.oracle).bind fun selected =>
                (PMF.uniformOfFintype InputMacKey).map fun key =>
                  (base.table, selected.1, {base with inputKey := key, oracle := selected.2.1}, selected.2.2) := by
  unfold sharedIdealCircuitPrefix
  rw [sharedTape_bind]
  simp only [sharedRunCircuitSimulatorWithTranscript, PMF.map_comp, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind)
  funext oracles
  apply congrArg ((PMF.uniformOfFintype BaseField).bind)
  funext bridge
  rw [PMF.bind_comm]
  apply congrArg ((PMF.uniformOfFintype PublicSample).bind)
  funext sample
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

/-- Independent key resampling preserves the full shared adaptive prefix. -/
theorem sharedIdealCircuitPrefix_rekey :
    sharedIdealCircuitPrefix adversary parameter scalar auxiliary =
      (sharedIdealCircuitPrefix adversary parameter scalar auxiliary).bind fun prior =>
        (PMF.uniformOfFintype InputMacKey).map (sharedRekeyPrefix prior) := by
  simp only [sharedIdealCircuitPrefix_key, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    PMF.map, PMF.pure_bind, sharedRekeyPrefix, PMF.bind_const]

abbrev SharedPrefixLabelUses {State : Type*} (prior : SharedLabelPrefixState State) :=
  ∀ query : Fin (sharedFixedTranscriptRecords prior.2.2.2).length,
    Fin (sharedCircuitBucketSize ((sharedFixedTranscriptRecords prior.2.2.2).get query).index) → PrequeryLabelUse

/-- The source choices omit the private input key before the collision test. -/
def sharedIdealPrequeryLabelCollisionFlag {Extra : Type*}
    (extra : SharedLabelPrefixState adversary.State → PMF Extra)
    (uses : (prior : SharedLabelPrefixState adversary.State) → Extra → SharedPrefixLabelUses prior) : PMF Bool :=
  (sharedIdealCircuitPrefix adversary parameter scalar auxiliary).bind fun prior =>
    (extra (sharedErasePrefixKey prior)).map fun selected =>
      @decide (sharedPrequeryLabelCollision (sharedFixedTranscriptRecords prior.2.2.2)
        (uses (sharedErasePrefixKey prior) selected) prior.2.2.1.inputKey) (Classical.propDecidable _)

private theorem sharedPrequeryFlag_resample {Extra : Type*}
    (extra : SharedLabelPrefixState adversary.State → PMF Extra)
    (uses : (prior : SharedLabelPrefixState adversary.State) → Extra → SharedPrefixLabelUses prior) :
    sharedIdealPrequeryLabelCollisionFlag adversary parameter scalar auxiliary extra uses =
      (sharedIdealCircuitPrefix adversary parameter scalar auxiliary).bind fun prior =>
        (extra (sharedErasePrefixKey prior)).bind fun selected =>
          (PMF.uniformOfFintype InputMacKey).map fun key =>
            @decide (sharedPrequeryLabelCollision (sharedFixedTranscriptRecords prior.2.2.2)
              (uses (sharedErasePrefixKey prior) selected) key) (Classical.propDecidable _) := by
  unfold sharedIdealPrequeryLabelCollisionFlag
  conv_lhs => rw [sharedIdealCircuitPrefix_rekey, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply congrArg ((sharedIdealCircuitPrefix adversary parameter scalar auxiliary).bind)
  funext prior
  change (PMF.uniformOfFintype InputMacKey).bind (fun key =>
    (extra (sharedErasePrefixKey prior)).map (fun selected =>
      @decide (sharedPrequeryLabelCollision (sharedFixedTranscriptRecords prior.2.2.2)
        (uses (sharedErasePrefixKey prior) selected) key) (Classical.propDecidable _))) = _
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

/-- The actual shared prefix records at most the permitted number of queries. -/
theorem sharedIdealCircuitPrefix_length_le
    (prior : SharedLabelPrefixState adversary.State)
    (member : prior ∈ (sharedIdealCircuitPrefix adversary parameter scalar auxiliary).support) :
    (sharedFixedTranscriptRecords prior.2.2.2).length ≤ adversary.firstQueryBudget parameter := by
  simp only [sharedIdealCircuitPrefix, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨state, _, selected, selectedMember, rfl⟩ := member
  exact (sharedFixedTranscriptRecords_length selected.2.2).trans
    (runOracleProgramWithTranscript_length_le _ _ _ _ selectedMember)

/-- The actual adaptive prefix pays at most 364 inverse blocks per query. -/
theorem sharedIdealPrequeryLabelCollisionFlag_mass_le [Fintype Block] {Extra : Type*}
    (extra : SharedLabelPrefixState adversary.State → PMF Extra)
    (uses : (prior : SharedLabelPrefixState adversary.State) → Extra → SharedPrefixLabelUses prior) :
    (sharedIdealPrequeryLabelCollisionFlag adversary parameter scalar auxiliary extra uses).toOuterMeasure
      {flag | flag = true} ≤
        (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  rw [sharedPrequeryFlag_resample]
  apply Probability.bind_event_le
  intro prior member
  apply Probability.bind_event_le
  intro selected _
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  simp only [decide_eq_true_eq]
  have bound := sharedPrequeryLabelCollision_mass_le (sharedFixedTranscriptRecords prior.2.2.2)
    (uses (sharedErasePrefixKey prior) selected)
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card, Nat.cast_pow, Nat.cast_ofNat] at bound
  apply bound.trans
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 364
    (sharedIdealCircuitPrefix_length_le adversary parameter scalar auxiliary prior member)

end
end Kriterion.ArgoMAC.Security
