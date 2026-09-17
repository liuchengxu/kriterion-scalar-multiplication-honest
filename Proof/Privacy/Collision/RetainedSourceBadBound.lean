import Proof.Privacy.Collision.ActualPrequeryCollision
import Proof.Privacy.Source.AdaptiveGateSourceDistribution
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype publicVectorFintype ciphertextFintype bitAdaptorTableFintype
  instFintypeHiddenGateSample instFintypeHiddenRowSample instNonemptyHiddenPublicSample
local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty VisibleSimulatorCoin := ⟨(SimulatorCoin.visibleHiddenEquiv defaultSimulatorCoin).1⟩

/-- The retained row family excludes all oracle and bridge fields. -/
theorem retainedSourceRows_fields [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (offsets : ClampedAffineOffsets) (rhos : Fin outputMacCount → NonZeroBase)
    (field otherField : BaseField × NonZeroBase) (oracles otherOracles : GarblingOracleData) :
    retainedSourceRows scalar (offsets, rhos, field, oracles) =
      retainedSourceRows scalar (offsets, rhos, otherField, otherOracles) := by
  rfl

def retainedSourceBirthday (sample : PublicSample) (rows : Rows) (input : AffineInput) : Prop :=
  pointBranchCollision (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).1)
    (fun row => rows.get row) input (fun row => (evaluateRowsCubic rows input).get row)
    (fun row => (RowPublicSample.visibleHiddenEquiv (sample.points.get row)).2)

private theorem retainedSourceBirthday_hidden (visible : VisiblePublicSample) (hidden : HiddenPublicSample)
    (rows : Rows) (input : AffineInput) :
    retainedSourceBirthday (PublicSample.visibleHiddenEquiv.symm (visible, hidden)) rows input =
      pointBranchCollision visible.2 (fun row => rows.get row) input
        (fun row => (evaluateRowsCubic rows input).get row) hidden.2 := by
  unfold retainedSourceBirthday
  have rowLaw (row : Fin outputMacCount) :
      (PublicSample.visibleHiddenEquiv.symm (visible, hidden)).points.get row =
        RowPublicSample.visibleHiddenEquiv.symm (visible.2 row, hidden.2 row) := Vector.get_ofFn _ _
  simp only [rowLaw, Equiv.apply_symm_apply]

universe uAux
variable {Aux : Type uAux}
  (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec
    AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

def retainedSourceKernel (rows : Rows) (mask : BaseField) : ActualPrefixSourceKernel adversary :=
  fun sample _ bridge selected _ _ => PMF.pure (circuitMaskSampleSplit bridge mask rows selected.1 sample).2

def retainedBirthdayFlag (rows : Rows) : PMF Bool :=
  (PMF.uniformOfFintype SimulatorCoin).bind fun coin =>
    (actualCoinPrefix adversary parameter auxiliary coin).map fun selected =>
      @decide (retainedSourceBirthday coin.tableSample rows selected.1.1) (Classical.propDecidable _)

private theorem actualCoinPrefix_hidden (visible : VisibleSimulatorCoin) (hidden : HiddenPublicSample) :
    actualCoinPrefix adversary parameter auxiliary (SimulatorCoin.visibleHiddenEquiv.symm (visible, hidden)) =
      actualCoinPrefix adversary parameter auxiliary
        (SimulatorCoin.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample)) := by
  unfold actualCoinPrefix
  rw [simulatorCoin_hidden_table visible hidden (Classical.arbitrary HiddenPublicSample),
    simulatorCoin_hidden_oracle visible hidden (Classical.arbitrary HiddenPublicSample)]

theorem retainedBirthdayFlag_resample (rows : Rows) :
    retainedBirthdayFlag adversary parameter auxiliary rows =
      (PMF.uniformOfFintype VisibleSimulatorCoin).bind fun visible =>
        (actualCoinPrefix adversary parameter auxiliary
          (SimulatorCoin.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample))).bind fun selected =>
          (PMF.uniformOfFintype HiddenPublicSample).map fun hidden =>
            @decide (pointBranchCollision visible.1.2 (fun row => rows.get row) selected.1.1
              (fun row => (evaluateRowsCubic rows selected.1.1).get row) hidden.2) (Classical.propDecidable _) := by
  classical
  unfold retainedBirthdayFlag
  rw [uniform_simulatorCoin_split]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype VisibleSimulatorCoin).bind
  funext visible
  simp_rw [actualCoinPrefix_hidden adversary parameter auxiliary visible]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  apply congrArg (actualCoinPrefix adversary parameter auxiliary
    (SimulatorCoin.visibleHiddenEquiv.symm (visible, Classical.arbitrary HiddenPublicSample))).bind
  funext selected
  apply congrArg (PMF.uniformOfFintype HiddenPublicSample).bind
  funext hidden
  change PMF.pure (@decide (retainedSourceBirthday
    (PublicSample.visibleHiddenEquiv.symm (visible.1, hidden)) rows selected.1.1) _) = _
  rw [retainedSourceBirthday_hidden]
  rfl

private theorem bind_bound {Source Target : Type*}
    (source : PMF Source) (next : Source → PMF Target) (event : Set Target) (bound : ENNReal)
    (pointwise : ∀ value, (next value).toOuterMeasure event ≤ bound) :
    (source.bind next).toOuterMeasure event ≤ bound := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc
    _ ≤ ∑' value, source value * bound :=
      ENNReal.tsum_le_tsum (fun value => mul_le_mul_right (pointwise value) _)
    _ = bound := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem retainedBirthdayFlag_mass_le [Fintype Block] (rows : Rows) :
    (retainedBirthdayFlag adversary parameter auxiliary rows).toOuterMeasure {flag | flag = true} ≤
      224668080 / (2 : ENNReal) ^ 128 := by
  rw [retainedBirthdayFlag_resample]
  apply bind_bound
  intro visible
  apply bind_bound
  intro selected
  rw [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  simp only [decide_eq_true_eq]
  exact @pointBranchCollision_fullTape_mass_le_blocks ‹Fintype Block› visible.1.2
    (fun row => rows.get row) selected.1.1 (fun row => (evaluateRowsCubic rows selected.1.1).get row)

/-- These flags retain the actual source prescription before output replacement. -/
def retainedJointSourceFlags (rows : Rows) (mask : BaseField) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype SimulatorCoin).bind fun coin =>
    (actualCoinPrefix adversary parameter auxiliary coin).map fun selected =>
      let source := (circuitMaskSampleSplit coin.bridgeKey mask rows selected.1.1 coin.tableSample).2
      (@decide (retainedSourceBirthday coin.tableSample rows selected.1.1) (Classical.propDecidable _),
        @decide (prequeryLabelCollision (fixedOracleTranscriptRecords selected.2.2)
          (sourcePrequeryLabelUses coin.oracles coin.bridgeKey source
            (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
            (fixedOracleTranscriptRecords selected.2.2)) coin.inputKey) (Classical.propDecidable _))

theorem retainedJointSourceFlags_fst (rows : Rows) (mask : BaseField) :
    (retainedJointSourceFlags adversary parameter auxiliary rows mask).map Prod.fst =
      retainedBirthdayFlag adversary parameter auxiliary rows := by
  simp only [retainedJointSourceFlags, retainedBirthdayFlag, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem retainedJointSourceFlags_snd (rows : Rows) (mask : BaseField) :
    (retainedJointSourceFlags adversary parameter auxiliary rows mask).map Prod.snd =
      actualSourcePrequeryFlag adversary parameter auxiliary (retainedSourceKernel adversary rows mask) := by
  simp only [retainedJointSourceFlags, actualSourcePrequeryFlag, retainedSourceKernel,
    PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

/-- The retained actual prescription pays one birthday loss and one prefix loss. -/
theorem retainedJointSourceFlags_mass_le [Fintype Block] (rows : Rows) (mask : BaseField) :
    (retainedJointSourceFlags adversary parameter auxiliary rows mask).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        224668080 / (2 : ENNReal) ^ 128 +
          (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  have first := retainedBirthdayFlag_mass_le adversary parameter auxiliary rows
  rw [← retainedJointSourceFlags_fst adversary parameter auxiliary rows mask,
    PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at first
  have second := actualSourcePrequeryFlag_mass_le adversary parameter auxiliary
    (retainedSourceKernel adversary rows mask)
  rw [← retainedJointSourceFlags_snd adversary parameter auxiliary rows mask,
    PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at second
  exact (MeasureTheory.measure_union_le _ _).trans (add_le_add first second)

/-- The birthday flag certifies the exact retained source offsets. -/
theorem retainedSource_rawOffset_injective (sample : PublicSample) (bridgeKey mask : BaseField)
    (rows : Rows) (sparse : ∀ row, SparseRow (rows.get row)) (input : AffineInput)
    (good : ¬ retainedSourceBirthday sample rows input)
    (pointKey curveKey : InputMacKey) (index : Pipeline.FixedKeyIndex) :
    let source := (circuitMaskSampleSplit bridgeKey mask rows input sample).2
    Function.Injective (rawBucketOffset (sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index) := by
  dsimp only
  rw [← reconstructedCircuitSource_eq_split bridgeKey mask rows sparse input sample]
  exact reconstructedCircuitSource_rawOffset_injective sample mask (fun row => rows.get row) input
    (bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2))
    (fun row => (evaluateRowsCubic rows input).get row) good pointKey curveKey index

/-- Averaging independent retained rows and masks preserves the same loss. -/
theorem retainedJointSourceFlags_mixture_mass_le [Fintype Block] (source : PMF (Rows × BaseField)) :
    (source.bind (fun fields => retainedJointSourceFlags adversary parameter auxiliary fields.1 fields.2)).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        224668080 / (2 : ENNReal) ^ 128 +
          (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  apply bind_bound
  intro fields
  exact retainedJointSourceFlags_mass_le adversary parameter auxiliary fields.1 fields.2

/-- The retained flags certify the exact source schedule used before output replacement. -/
theorem retainedSource_schedule_fresh (coin : SimulatorCoin) (state : SimulatorState)
    (rows : Rows) (sparse : ∀ row, SparseRow (rows.get row)) (input : AffineInput) (mask : BaseField)
    (pointGood : ¬ retainedSourceBirthday coin.tableSample rows input)
    (prefixGood : let source := (circuitMaskSampleSplit coin.bridgeKey mask rows input coin.tableSample).2
      ¬ prequeryLabelCollision state.fixedTranscript
        (sourcePrequeryLabelUses coin.oracles coin.bridgeKey source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) state.fixedTranscript)
        coin.inputKey) :
    let selected := coin.tableSample.retargetMask input
      (coin.bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2)) (evaluateRowsCubic rows input)
    let pointKey := EncPRF.transformKey coin.oracles.encOracle
      (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
    FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (pipelineGateSchedule selected.curveRequest selected.pointRequests input
        (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input))) := by
  dsimp only
  rw [← circuitMaskSampleGarble_split coin.bridgeKey mask rows sparse input coin.tableSample]
  apply circuitMaskSchedule_fresh
  · exact retainedSource_rawOffset_injective coin.tableSample coin.bridgeKey mask rows sparse input
      pointGood _ coin.inputKey
  · intro gate slot _
    exact sourcePrequeryLabelCollision_false_fresh coin.oracles coin.bridgeKey _ _
      state.fixedTranscript coin.inputKey prefixGood gate slot

end
end Kriterion.ArgoMAC.Security
