import Proof.Privacy.Collision.RetainedSourceBadBound
import Proof.Privacy.Source.RetainedSourceTransport
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype publicVectorFintype ciphertextFintype bitAdaptorTableFintype
  instNonemptyPublicSample_2 circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable, fun _ _ => defaultHashLiftQuotient)⟩
local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance [FieldCertificate] [GroupCertificate] : Nonempty RetainedRowCoin :=
  ⟨(Classical.arbitrary ClampedAffineOffsets, fun _ => (Seed.randomness 0).curveMask,
    (Seed.randomness 0).curveMask)⟩

private theorem uniform_pair_bind {A B C : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (next : A → B → PMF C) :
    (PMF.uniformOfFintype A).bind (fun a => (PMF.uniformOfFintype B).bind (next a)) =
      (PMF.uniformOfFintype (A × B)).bind (fun pair => next pair.1 pair.2) := by
  conv_rhs => rw [uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

private theorem collisionLoss_toReal (budget : Nat) :
    (224668080 / (2 : ENNReal) ^ 128 + (182 * budget : Nat) / (2 : ENNReal) ^ 128).toReal =
      224668080 / (2 : ℝ) ^ 128 + (182 * budget : Nat) / (2 : ℝ) ^ 128 := by
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]

private theorem collisionLoss_real_bound (budget : Nat) (probability : ENNReal)
    (bound : probability ≤ 224668080 / (2 : ENNReal) ^ 128 + (182 * budget : Nat) / (2 : ENNReal) ^ 128) :
    probability.toReal ≤ 224668080 / (2 : ℝ) ^ 128 + (182 * budget : Nat) / (2 : ℝ) ^ 128 := by
  rw [← collisionLoss_toReal]
  exact ENNReal.toReal_mono (by finiteness) bound

private theorem rounded_probability_bound (first second loss rounding : ℝ)
    (distance : |first - second| ≤ rounding) (bound : second ≤ loss) :
    first ≤ loss + rounding := by
  have upper := (abs_le.mp distance).2
  linarith

private theorem rounded_event_transport {first second first' second' : PMF Bool}
    (event : Set Bool) (loss rounding : ℝ)
    (distance : |(first'.toOuterMeasure event).toReal - (second'.toOuterMeasure event).toReal| ≤ rounding)
    (firstEq : first = first') (secondEq : second = second')
    (bound : (second.toOuterMeasure event).toReal ≤ loss) :
    (first.toOuterMeasure event).toReal ≤ loss + rounding := by
  rw [firstEq, secondEq] at *
  exact rounded_probability_bound _ _ _ _ distance bound

/-- This row family keeps exactly the retained offsets and rho values. -/
def retainedCoinRows [FieldCertificate] [GroupCertificate] (scalar : ScalarField) (rowCoin : RetainedRowCoin) : Rows :=
  retainedSourceRows scalar (retainedSimulatorSourceEquiv.symm (rowCoin, defaultSimulatorCoin)).1

theorem retainedCoinRows_inverse [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (rowCoin : RetainedRowCoin) (coin : SimulatorCoin) :
    retainedSourceRows scalar (retainedSimulatorSourceEquiv.symm (rowCoin, coin)).1 =
      retainedCoinRows scalar rowCoin := by
  apply retainedSourceRows_fields

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

def retainedFlagsAt (rows : Rows) (mask : BaseField) (coin : SimulatorCoin) : PMF (Bool × Bool) :=
  (actualCoinPrefix adversary parameter auxiliary coin).map fun selected =>
    let source := (circuitMaskSampleSplit coin.bridgeKey mask rows selected.1.1 coin.tableSample).2
    (@decide (retainedSourceBirthday coin.tableSample rows selected.1.1) (Classical.propDecidable _),
      @decide (prequeryLabelCollision (fixedOracleTranscriptRecords selected.2.2)
        (sourcePrequeryLabelUses coin.oracles coin.bridgeKey source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
          (fixedOracleTranscriptRecords selected.2.2)) coin.inputKey) (Classical.propDecidable _))

/-- This distribution keeps every actual retained field and the uniform public sample. -/
def concreteRetainedFlags [FieldCertificate] [GroupCertificate] (scalar : ScalarField) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype (MaskRetainedTape × PublicSample)).bind fun source =>
    retainedFlagsAt adversary parameter auxiliary (retainedSourceRows scalar source.1)
      source.1.2.2.1.2.value (simulatorSourceEquiv (source.1.2.2, source.2)).1

theorem concreteRetainedFlags_split [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    concreteRetainedFlags adversary parameter auxiliary scalar =
      (PMF.uniformOfFintype RetainedRowCoin).bind fun rowCoin =>
        retainedJointSourceFlags adversary parameter auxiliary (retainedCoinRows scalar rowCoin) rowCoin.2.2.value := by
  have law := congrArg (fun distribution => distribution.bind (fun source : RetainedRowCoin × SimulatorCoin =>
    retainedFlagsAt adversary parameter auxiliary (retainedCoinRows scalar source.1) source.1.2.2.value source.2))
    map_uniform_retainedSimulatorSource
  rw [PMF.bind_map] at law
  have inverse (source : MaskRetainedTape × PublicSample) :
      retainedCoinRows scalar (retainedSimulatorSourceEquiv source).1 = retainedSourceRows scalar source.1 := by
    have rows := retainedCoinRows_inverse scalar (retainedSimulatorSourceEquiv source).1
      (retainedSimulatorSourceEquiv source).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at rows
    exact rows.symm
  simp only [Function.comp_def, inverse] at law
  change concreteRetainedFlags adversary parameter auxiliary scalar = _ at law
  rw [law, uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  rfl

/-- The exact actual retained source has the joint collision bound. -/
theorem concreteRetainedFlags_mass_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (scalar : ScalarField) :
    (concreteRetainedFlags adversary parameter auxiliary scalar).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        224668080 / (2 : ENNReal) ^ 128 +
          (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  rw [concreteRetainedFlags_split]
  apply Probability.bind_event_le
  intro rowCoin _
  exact retainedJointSourceFlags_mass_le adversary parameter auxiliary
    (retainedCoinRows scalar rowCoin) rowCoin.2.2.value

/-- This event tests the exact raw prescription and its complete prefix. -/
def rawSourceBad (coin : SimulatorCoin) (source : CircuitMaskSample) (input : AffineInput)
    (history : List (Sigma Garbling.oracleSpec.Answer)) : Prop :=
  let lifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
  let pointKey := EncPRF.transformKey coin.oracles.encOracle
    (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
  let gates := sourceGatePrescription source pointKey coin.inputKey lifts
  (¬ ∀ index, Function.Injective (rawBucketOffset gates index)) ∨
    (¬ ∀ gate slot,
      rawSlotBranch slot = circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) →
      (OnCurve input ∨ ∃ adaptor bit, gate = .inl (adaptor, bit)) →
      let record := (gates gate).slotRecord slot
      FreshPermutationPair (fixedOracleTranscriptRecords history) record.index record.domain record.range)

/-- The source observer uses the same initial oracles as the actual input program. -/
def maskSourceBadObserver [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : MaskRetainedTape) (source : CircuitMaskSample) : PMF Bool :=
  let coin := (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter
      (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value (retainedSourceRows scalar retained) source)
      auxiliary) coin.state.oracle).map fun selected =>
        @decide (rawSourceBad coin source selected.1.1 selected.2.2) (Classical.propDecidable _)

set_option backward.isDefEq.respectTransparency false in
private theorem maskSourceBadObserver_public [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : MaskRetainedTape) :
    (PMF.uniformOfFintype CircuitMaskSample).bind (maskSourceBadObserver adversary parameter auxiliary scalar retained) =
      (PMF.uniformOfFintype PublicSample).bind fun sample =>
        let coin := (simulatorSourceEquiv (retained.2.2, sample)).1
        (actualCoinPrefix adversary parameter auxiliary coin).map fun selected =>
          @decide (rawSourceBad coin
            (circuitMaskSampleSplit coin.bridgeKey retained.2.2.1.2.value
              (retainedSourceRows scalar retained) selected.1.1 sample).2 selected.1.1 selected.2.2) (Classical.propDecidable _) := by
  unfold maskSourceBadObserver
  let coin := (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
  let choose := fun table => (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) coin.state.oracle).map fun selected => (selected.1.1, selected)
  have law := adaptiveRetainedSource_observation_eq retained.2.2.1.1 retained.2.2.1.2.value
    (retainedSourceRows scalar retained) (rowsForOutputKeysSparse _ _) choose
    (fun selected source => PMF.pure (@decide (rawSourceBad coin source selected.1 selected.2.2.2) (Classical.propDecidable _)))
  simpa only [maskSourceBadObserver, choose, PMF.bind_map, PMF.map, PMF.bind_bind,
    PMF.pure_bind, Function.comp_def, actualCoinPrefix, coin, simulatorSourceEquiv, Equiv.coe_fn_mk,
    SimulatorCoin.state, CircuitSimulatorState.table, publicMaskTable, rawSourceBad] using law

private theorem rawSourceBadAt_le (rows : Rows) (sparse : ∀ row, SparseRow (rows.get row))
    (mask : BaseField) (coin : SimulatorCoin) :
    ((actualCoinPrefix adversary parameter auxiliary coin).map (fun selected =>
      @decide (rawSourceBad coin (circuitMaskSampleSplit coin.bridgeKey mask rows selected.1.1 coin.tableSample).2
        selected.1.1 selected.2.2) (Classical.propDecidable _))).toOuterMeasure {flag | flag = true} ≤
      (retainedFlagsAt adversary parameter auxiliary rows mask coin).toOuterMeasure
        {flags | flags.1 = true ∨ flags.2 = true} := by
  simp only [retainedFlagsAt, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq, decide_eq_true_eq]
  apply MeasureTheory.measure_mono
  intro selected bad
  rcases bad with offsetBad | prefixBad
  · left
    by_contra pointGood
    apply offsetBad
    exact retainedSource_rawOffset_injective coin.tableSample coin.bridgeKey mask rows sparse
      selected.1.1 pointGood _ coin.inputKey
  · right
    by_contra prefixGood
    apply prefixBad
    intro gate slot _ _
    exact sourcePrequeryLabelCollision_false_fresh coin.oracles coin.bridgeKey
      (circuitMaskSampleSplit coin.bridgeKey mask rows selected.1.1 coin.tableSample).2 _
      (fixedOracleTranscriptRecords selected.2.2) coin.inputKey prefixGood gate slot

/-- This source keeps the exact retained tape and independent complete mask source. -/
def goodRetainedBadSource [FieldCertificate] [GroupCertificate] (scalar : ScalarField) : PMF Bool :=
  (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
    (PMF.uniformOfFintype CircuitMaskSample).bind (maskSourceBadObserver adversary parameter auxiliary scalar retained)

private theorem goodRetainedBadSource_public [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    goodRetainedBadSource adversary parameter auxiliary scalar =
      (PMF.uniformOfFintype (MaskRetainedTape × PublicSample)).bind fun source =>
        let coin := (simulatorSourceEquiv (source.1.2.2, source.2)).1
        (actualCoinPrefix adversary parameter auxiliary coin).map fun selected =>
          @decide (rawSourceBad coin (circuitMaskSampleSplit coin.bridgeKey source.1.2.2.1.2.value
            (retainedSourceRows scalar source.1) selected.1.1 source.2).2 selected.1.1 selected.2.2) (Classical.propDecidable _) := by
  unfold goodRetainedBadSource
  simp_rw [maskSourceBadObserver_public]
  exact uniform_pair_bind _

/-- The complete actual mask source satisfies the checked joint loss. -/
theorem goodRetainedBadSource_mass_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (scalar : ScalarField) :
    (goodRetainedBadSource adversary parameter auxiliary scalar).toOuterMeasure {flag | flag = true} ≤
      224668080 / (2 : ENNReal) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  apply le_trans _ (concreteRetainedFlags_mass_le adversary parameter auxiliary scalar)
  rw [goodRetainedBadSource_public, concreteRetainedFlags]
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  apply ENNReal.tsum_le_tsum
  intro source
  apply mul_le_mul_right
  exact rawSourceBadAt_le adversary parameter auxiliary (retainedSourceRows scalar source.1)
    (rowsForOutputKeysSparse _ _) source.1.2.2.1.2.value _

/-- A complete decoded source retains every original full hash value. -/
theorem decodeFullSource_lifts (source : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete source.1) :
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv (decodeFullSource source)).1 gate)) = source.1 := by
  funext gate
  simp only [decodeFullSource, Equiv.apply_symm_apply]
  obtain ⟨pair, same⟩ := complete gate
  rw [← same]
  simp only [fullSourceHashPair_good]

/-- The full-source flag also rejects incomplete hash fibers. -/
def fullRetainedBadObserver [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : MaskRetainedTape) (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : PMF Bool := by
  classical
  exact if FullSourceComplete source.1 then
    maskSourceBadObserver adversary parameter auxiliary scalar retained (decodeFullSource source)
  else PMF.pure true

private theorem fullRetainedBadObserver_good [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : MaskRetainedTape)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) :
    retainedGoodHashObserver (fullRetainedBadObserver adversary parameter auxiliary scalar) retained source =
      maskSourceBadObserver adversary parameter auxiliary scalar retained (circuitMaskHashSplitEquiv.symm source) := by
  have complete : FullSourceComplete (fun gate => goodHashLiftSource (source.1 gate)) :=
    fun gate => ⟨source.1 gate, rfl⟩
  rw [retainedGoodHashObserver, fullRetainedBadObserver, if_pos complete]
  simp only [decodeFullSource, fullSourceHashPair_good]

/-- This flag uses the exact full-source sampling law used by the source ratio. -/
def fullRetainedBadSource [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (witness : Garbling.Randomness) : PMF Bool :=
  (randomTape witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun source =>
      fullRetainedBadObserver adversary parameter auxiliary scalar (maskRetainedTape randomness)
        (source.1, sharedCircuitHashRest randomness source.2)

private theorem goodSharedRetainedBadSource_eq [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (witness : Garbling.Randomness) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
        retainedGoodHashObserver (fullRetainedBadObserver adversary parameter auxiliary scalar)
          (maskRetainedTape randomness) (source.1, sharedCircuitHashRest randomness source.2)) =
      goodRetainedBadSource adversary parameter auxiliary scalar := by
  rw [sharedHashSource_observation_eq witness parameter
    (retainedGoodHashObserver (fullRetainedBadObserver adversary parameter auxiliary scalar))]
  simp_rw [fullRetainedBadObserver_good]
  rw [PMF.bind_comm]
  unfold goodRetainedBadSource
  apply congrArg (PMF.uniformOfFintype MaskRetainedTape).bind
  funext retained
  rw [← map_uniform_circuitMaskHashSplit, PMF.bind_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

/-- The actual full source pays the joint collision loss and the exact hash rounding loss. -/
theorem fullRetainedBadSource_mass_le [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (witness : Garbling.Randomness) :
    ((fullRetainedBadSource adversary parameter auxiliary scalar witness).toOuterMeasure {flag | flag = true}).toReal ≤
      224668080 / (2 : ℝ) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have rounding := sharedRetainedHash_observation_bound witness parameter
    (fullRetainedBadObserver adversary parameter auxiliary scalar) {flag | flag = true}
  have good := goodRetainedBadSource_mass_le adversary parameter auxiliary scalar
  have goodReal := collisionLoss_real_bound (adversary.firstQueryBudget parameter) _ good
  exact rounded_event_transport {flag | flag = true} _ _ rounding rfl
    (goodSharedRetainedBadSource_eq adversary parameter auxiliary scalar witness).symm goodReal

end
end Kriterion.ArgoMAC.Security
