import Proof.Privacy.Collision.IdealCollisionBound
import Proof.Privacy.Distribution.EncPRFDistribution
import Proof.Privacy.Collision.CircuitSlotRatio

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] publicInputMacKeyFintype

local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem uniform_function_eval {Index Value : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Value] [Nonempty Value] (index : Index) :
    (PMF.uniformOfFintype (Index → Value)).map (fun values => values index) =
      PMF.uniformOfFintype Value := by
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween (Equiv.piSplitAt index (fun _ => Value)))
  simpa only [PMF.map_comp, map_uniform_prod_fst, Function.comp_def, Equiv.piSplitAt_apply] using law

/-- Each actual source label is uniform under the complete input-key law. -/
theorem uniform_inputKeyLabel [Fintype Block] (index : EncPRF.PermutationIndex) (bit : Bool) :
    (PMF.uniformOfFintype InputMacKey).map (fun key => inputKeyLabel key index bit) =
      PMF.uniformOfFintype Block := by
  have evaluated := congrArg (fun distribution => distribution.map (fun labels => labels bit))
    (uniform_function_eval (Value := Bool → Block) index)
  rw [PMF.map_comp, uniform_function_eval] at evaluated
  have law := congrArg (fun distribution => distribution.map (fun labels => labels index bit))
    (map_uniformOfFintype_equivBetween inputKeyLabelEquiv)
  rw [PMF.map_comp] at law
  exact law.trans evaluated

/-- Fixed H/EncPRF data makes each actual linked label a fixed shift of its source. -/
theorem linkedLabel_fixedShift (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (key : InputMacKey) (index : EncPRF.PermutationIndex) (bit : Bool) :
    inputKeyLabel (EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) index bit =
      inputKeyLabel key index bit ^^^ evenMansour (oracle.encOracle.permutation index)
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) bit := by
  rw [inputKeyLabel_transform]
  exact BitVec.xor_comm _ _

/-- One bucket use fixes the label index and both query shifts before key sampling. -/
structure PrequeryLabelUse where
  index : EncPRF.PermutationIndex
  bit : Bool
  domainShift : Block
  rangeShift : Block


/-- Every actual gate reads one source coordinate label. -/
def circuitGateWire : RawCircuitGate → EncPRF.PermutationIndex
  | .inl (adaptor, bit) => (![(.x : EncPRF.Coordinate), .x, .x, .y, .y] adaptor, bit)
  | .inr (_, .inl (adaptor, bit)) => (![(.y : EncPRF.Coordinate), .y, .y, .x] adaptor, bit)
  | .inr (_, .inr (.inl (adaptor, bit))) => (![(.x : EncPRF.Coordinate), .x, .x] adaptor, bit)
  | .inr (_, .inr (.inr (adaptor, bit))) => (![(.y : EncPRF.Coordinate), .y, .y, .x, .x] adaptor, bit)

/-- Curve labels have no linking pad. Point labels use the actual fixed EncPRF pad. -/
def circuitGateLabelPad (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (gate : RawCircuitGate) (bit : Bool) : Block :=
  match gate with
  | .inl _ => 0
  | .inr _ => evenMansour (oracle.encOracle.permutation (circuitGateWire gate))
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) bit

/-- This identity includes the actual EncPRF link for every selected gate label. -/
theorem circuitGateLabel_sourceShift (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (key : InputMacKey) (gate : RawCircuitGate) (bit : Bool) :
    BitAdaptor.encode (circuitGateKey (EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) key gate) bit =
    inputKeyLabel key (circuitGateWire gate) bit ^^^ circuitGateLabelPad oracle bridgeKey gate bit := by
  rcases gate with ⟨adaptor, position⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;> simp [circuitGateKey, circuitGateWire, circuitGateLabelPad, inputKeyLabel]
  · rcases gate with ⟨adaptor, position⟩ | (⟨adaptor, position⟩ | ⟨adaptor, position⟩)
    · fin_cases adaptor
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit
    · fin_cases adaptor
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit
    · fin_cases adaptor
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.y, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit
      · exact linkedLabel_fixedShift oracle bridgeKey key (.x, position) bit

/-- This use records the actual tweaked domain and the actual programmed output shift. -/
def actualGateLabelUse (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (gate : RawCircuitGate) (bit : Bool) (outputBlock : Block) : PrequeryLabelUse :=
  ⟨circuitGateWire gate, bit,
    circuitGateLabelPad oracle bridgeKey gate bit ^^^ (rawCircuitLocation gate).tweak,
    circuitGateLabelPad oracle bridgeKey gate bit ^^^ outputBlock⟩

/-- The use gives the exact actual gate domain. -/
theorem actualGateLabelUse_domain (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (key : InputMacKey) (gate : RawCircuitGate) (bit : Bool) (outputBlock : Block) :
    let use := actualGateLabelUse oracle bridgeKey gate bit outputBlock
    inputKeyLabel key use.index use.bit ^^^ use.domainShift =
      BitAdaptor.encode (circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) key gate) bit ^^^
          (rawCircuitLocation gate).tweak := by
  dsimp only [actualGateLabelUse]
  rw [circuitGateLabel_sourceShift, BitVec.xor_assoc]

/-- The use gives the exact actual programmed range. -/
theorem actualGateLabelUse_range (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (key : InputMacKey) (gate : RawCircuitGate) (bit : Bool) (outputBlock : Block) :
    let use := actualGateLabelUse oracle bridgeKey gate bit outputBlock
    inputKeyLabel key use.index use.bit ^^^ use.rangeShift =
      outputBlock ^^^ BitAdaptor.encode (circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) key gate) bit := by
  dsimp only [actualGateLabelUse]
  rw [circuitGateLabel_sourceShift]
  ac_rfl

/-- This event covers both domain and range conflicts with the actual fixed-query history. -/
def prequeryLabelCollision
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (circuitBucketSize (history.get query).index) →
      PrequeryLabelUse) (key : InputMacKey) : Prop :=
  ∃ query row,
    let use := uses query row
    inputKeyLabel key use.index use.bit ^^^ use.domainShift = (history.get query).domain ∨
      inputKeyLabel key use.index use.bit ^^^ use.rangeShift = (history.get query).range

private theorem uniform_inputKeyLabel_xor_mass [Fintype Block]
    (index : EncPRF.PermutationIndex) (bit : Bool) (shift target : Block) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | inputKeyLabel key index bit ^^^ shift = target} =
        (Fintype.card Block : ENNReal)⁻¹ := by
  have law := congrArg (fun distribution => distribution.map (fun label => label ^^^ shift))
    (uniform_inputKeyLabel index bit)
  have shifted := map_uniformOfFintype_equivBetween (Pipeline.tweakEquiv shift)
  change (PMF.uniformOfFintype Block).map (fun label => label ^^^ shift) = _ at shifted
  rw [PMF.map_comp, shifted] at law
  have mass := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure {target}) law
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at mass
  exact mass

/-- Every fixed prefix query adds at most 182 inverse-block units of collision mass. -/
theorem prequeryLabelCollision_mass_le [Fintype Block]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (circuitBucketSize (history.get query).index) →
      PrequeryLabelUse) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | prequeryLabelCollision history uses key} ≤
        (182 * history.length : Nat) / (Fintype.card Block : ENNReal) := by
  classical
  rw [show {key | prequeryLabelCollision history uses key} =
      ⋃ query, ⋃ row, {key |
        inputKeyLabel key (uses query row).index (uses query row).bit ^^^
          (uses query row).domainShift = (history.get query).domain} ∪
        {key | inputKeyLabel key (uses query row).index (uses query row).bit ^^^
          (uses query row).rangeShift = (history.get query).range} by
    ext key
    simp only [prequeryLabelCollision, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union]]
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  calc
    _ ≤ ∑ query : Fin history.length,
        (2 * circuitBucketSize (history.get query).index : Nat) /
          (Fintype.card Block : ENNReal) := by
      apply Finset.sum_le_sum
      intro query _
      apply (MeasureTheory.measure_iUnion_le _).trans
      rw [tsum_fintype]
      calc
        _ ≤ ∑ _row : Fin (circuitBucketSize (history.get query).index),
            2 * (Fintype.card Block : ENNReal)⁻¹ := by
          apply Finset.sum_le_sum
          intro row _
          exact (MeasureTheory.measure_union_le _ _).trans (by
            rw [uniform_inputKeyLabel_xor_mass, uniform_inputKeyLabel_xor_mass]
            exact le_of_eq (two_mul _).symm)
        _ = _ := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ ∑ _query : Fin history.length, (182 : ENNReal) / Fintype.card Block := by
      apply Finset.sum_le_sum
      intro query _
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.mul_le_mul_left 2 (circuitBucketSize_le (history.get query).index)
    _ = _ := by simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]

/-- This update changes only the hidden source labels in the actual simulator coin. -/
def SimulatorCoin.rekey (coin : SimulatorCoin) (key : InputMacKey) : SimulatorCoin :=
  { coin with inputKey := key }

private def simulatorCoinKeySwap : (SimulatorCoin × InputMacKey) ≃ (SimulatorCoin × InputMacKey) where
  toFun pair := (pair.1.rekey pair.2, pair.1.inputKey)
  invFun pair := (pair.1.rekey pair.2, pair.1.inputKey)
  left_inv pair := by rcases pair with ⟨⟨sample, oracles, key, bridge⟩, other⟩; rfl
  right_inv pair := by rcases pair with ⟨⟨sample, oracles, key, bridge⟩, other⟩; rfl

local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩

/-- The complete offline law permits independent source-key resampling. -/
theorem uniform_simulatorCoin_rekey :
    PMF.uniformOfFintype SimulatorCoin =
      (PMF.uniformOfFintype SimulatorCoin).bind fun coin =>
        (PMF.uniformOfFintype InputMacKey).map coin.rekey := by
  have same := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween simulatorCoinKeySwap)
  simp only [PMF.map_comp, map_uniform_prod_fst, Function.comp_def, Equiv.piSplitAt_apply] at same
  rw [uniform_prod_eq_bind, PMF.map_bind] at same
  simp only [PMF.map_comp, Function.comp_def, simulatorCoinKeySwap, Equiv.coe_fn_mk] at same
  simp only [PMF.map] at same
  rw [PMF.bind_comm] at same
  exact same.symm

/-- This type retains the full actual prefix state and both public transcript fields. -/
abbrev LabelPrefixState (State : Type*) :=
  Pipeline.Table × (AffineInput × State) × CircuitSimulatorState ×
    List (Sigma Garbling.oracleSpec.Answer)

/-- This operation resamples only the source key before encoding. -/
def rekeyPrefix {State : Type*} (prestate : LabelPrefixState State) (key : InputMacKey) :
    LabelPrefixState State :=
  (prestate.1, prestate.2.1, {prestate.2.2.1 with inputKey := key}, prestate.2.2.2)

/-- This view removes the source key before any later independent choice. -/
def erasePrefixKey {State : Type*} (prestate : LabelPrefixState State) : LabelPrefixState State :=
  rekeyPrefix prestate defaultSimulatorCoin.inputKey

@[simp] theorem erasePrefixKey_rekey {State : Type*}
    (prestate : LabelPrefixState State) (key : InputMacKey) :
    erasePrefixKey (rekeyPrefix prestate key) = erasePrefixKey prestate := rfl

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)

private def coinLabelPrefix (coin : SimulatorCoin) : PMF (LabelPrefixState adversary.State) :=
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter coin.state.table auxiliary) coin.state.oracle).map
    (fun selected => (coin.state.table, selected.1,
      {coin.state with oracle := selected.2.1}, selected.2.2))

private theorem idealCircuitPrefix_coin :
    idealCircuitPrefix adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype SimulatorCoin).bind (coinLabelPrefix adversary parameter auxiliary) := by
  simp only [idealCircuitPrefix_oracle, simulatorStateTape, PMF.bind_map]
  rfl

private theorem coinLabelPrefix_rekey (coin : SimulatorCoin) (key : InputMacKey) :
    coinLabelPrefix adversary parameter auxiliary (coin.rekey key) =
      (coinLabelPrefix adversary parameter auxiliary coin).map (fun prestate => rekeyPrefix prestate key) := by
  unfold coinLabelPrefix
  rw [PMF.map_comp]
  rfl

private theorem bind_resample {Source Key Output : Type*}
    (source : PMF Source) (keys : PMF Key) (rekey : Source → Key → Source)
    (change : Output → Key → Output) (run : Source → PMF Output)
    (resample : source = source.bind (fun value => keys.map (rekey value)))
    (preserved : ∀ value key, run (rekey value key) =
      (run value).map (fun output => change output key)) :
    source.bind run = (source.bind run).bind (fun output => keys.map (change output)) := by
  conv_lhs => rw [resample, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, preserved, PMF.bind_bind]
  apply congrArg source.bind
  funext value
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

/-- The actual adaptive prefix leaves the hidden source key independent. -/
theorem idealCircuitPrefix_rekey :
    idealCircuitPrefix adversary parameter scalar auxiliary =
      (idealCircuitPrefix adversary parameter scalar auxiliary).bind fun prestate =>
        (PMF.uniformOfFintype InputMacKey).map (rekeyPrefix prestate) := by
  rw [idealCircuitPrefix_coin]
  exact bind_resample _ _ SimulatorCoin.rekey rekeyPrefix _ uniform_simulatorCoin_rekey
    (coinLabelPrefix_rekey adversary parameter auxiliary)

/-- This family lists the actual gate uses for each external fixed query. -/
abbrev PrefixLabelUses {State : Type*} (prestate : LabelPrefixState State) :=
  ∀ query : Fin (fixedOracleTranscriptRecords prestate.2.2.2).length,
    Fin (circuitBucketSize ((fixedOracleTranscriptRecords prestate.2.2.2).get query).index) →
      PrequeryLabelUse

/-- The later target choice uses the complete prefix without its hidden source key. -/
def idealPrequeryLabelCollisionFlag {Extra : Type*}
    (extra : LabelPrefixState adversary.State → PMF Extra)
    (uses : (prestate : LabelPrefixState adversary.State) → Extra → PrefixLabelUses prestate) : PMF Bool :=
  (idealCircuitPrefix adversary parameter scalar auxiliary).bind fun prestate =>
    (extra (erasePrefixKey prestate)).map fun selected =>
      @decide (prequeryLabelCollision (fixedOracleTranscriptRecords prestate.2.2.2)
        (uses (erasePrefixKey prestate) selected) prestate.2.2.1.inputKey) (Classical.propDecidable _)

private theorem idealPrequeryLabelCollisionFlag_resample {Extra : Type*}
    (extra : LabelPrefixState adversary.State → PMF Extra)
    (uses : (prestate : LabelPrefixState adversary.State) → Extra → PrefixLabelUses prestate) :
    idealPrequeryLabelCollisionFlag adversary parameter scalar auxiliary extra uses =
    (idealCircuitPrefix adversary parameter scalar auxiliary).bind (fun prestate =>
      (extra (erasePrefixKey prestate)).bind fun selected =>
        (PMF.uniformOfFintype InputMacKey).map fun key =>
          @decide (prequeryLabelCollision (fixedOracleTranscriptRecords prestate.2.2.2)
            (uses (erasePrefixKey prestate) selected) key) (Classical.propDecidable _)) := by
  unfold idealPrequeryLabelCollisionFlag
  conv_lhs => rw [idealCircuitPrefix_rekey, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, erasePrefixKey_rekey]
  apply congrArg ((idealCircuitPrefix adversary parameter scalar auxiliary).bind)
  funext prestate
  change (PMF.uniformOfFintype InputMacKey).bind (fun key =>
    (extra (erasePrefixKey prestate)).map (fun selected =>
      @decide (prequeryLabelCollision (fixedOracleTranscriptRecords prestate.2.2.2)
        (uses (erasePrefixKey prestate) selected) key) (Classical.propDecidable _))) = _
  simp only [PMF.map]
  rw [PMF.bind_comm]
  rfl

private theorem idealCircuitPrefix_length_le
    (prestate : LabelPrefixState adversary.State)
    (member : prestate ∈ (idealCircuitPrefix adversary parameter scalar auxiliary).support) :
    (fixedOracleTranscriptRecords prestate.2.2.2).length ≤ adversary.firstQueryBudget parameter := by
  simp only [idealCircuitPrefix, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨state, _, selected, selectedMember, rfl⟩ := member
  exact (fixedOracleTranscriptRecords_length_le selected.2.2).trans
    (runOracleProgramWithTranscript_length_le _ _ _ _ selectedMember)

/-- The actual adaptive prefix pays both selected-label query conflicts at most once per use. -/
theorem idealPrequeryLabelCollisionFlag_mass_le [Fintype Block] {Extra : Type*}
    (extra : LabelPrefixState adversary.State → PMF Extra)
    (uses : (prestate : LabelPrefixState adversary.State) → Extra → PrefixLabelUses prestate) :
    (idealPrequeryLabelCollisionFlag adversary parameter scalar auxiliary extra uses).toOuterMeasure
      {flag | flag = true} ≤
        (182 * adversary.firstQueryBudget parameter : Nat) / (Fintype.card Block : ENNReal) := by
  rw [idealPrequeryLabelCollisionFlag_resample]
  apply Probability.bind_event_le
  intro prestate member
  apply Probability.bind_event_le
  intro selected _
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  simp only [decide_eq_true_eq]
  apply (prequeryLabelCollision_mass_le _ _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 182
    (idealCircuitPrefix_length_le adversary parameter scalar auxiliary prestate member)

/-- The actual block size gives the concrete pre-encode collision loss. -/
theorem idealPrequeryLabelCollisionFlag_mass_le_blocks [Fintype Block] {Extra : Type*}
    (extra : LabelPrefixState adversary.State → PMF Extra)
    (uses : (prestate : LabelPrefixState adversary.State) → Extra → PrefixLabelUses prestate) :
    (idealPrequeryLabelCollisionFlag adversary parameter scalar auxiliary extra uses).toOuterMeasure
      {flag | flag = true} ≤
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using
    idealPrequeryLabelCollisionFlag_mass_le adversary parameter scalar auxiliary extra uses

end

end Kriterion.ArgoMAC.Security
