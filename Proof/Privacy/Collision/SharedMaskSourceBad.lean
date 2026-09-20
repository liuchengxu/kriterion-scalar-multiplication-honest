import Proof.Privacy.Collision.SharedSourcePrefixGuard
import Proof.Privacy.Source.SharedGateSourceSupport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype publicVectorFintype
  ciphertextFintype bitAdaptorTableFintype instNonemptyPublicSample_2 circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance sourceBadRemainder {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable, fun _ _ => defaultHashLiftQuotient)⟩
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble sharedSourcePrefixBad

variable {Aux : Type*}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The observer checks the exact source schedule after the public input choice. -/
def sharedMaskSourceBadObserver [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape) (source : CircuitMaskSample) : PMF Bool :=
  let data := retained.val.2.2.2
  let rows := retainedSourceRows scalar retained.val
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter
      (circuitMaskSourceTable retained.val.2.2.1.1 retained.val.2.2.1.2.value rows source) auxiliary)
      (sharedInitialSourceOracle data)).map fun selected =>
        @decide (sharedSourcePrefixBad ⟨data.fixedKeyOracle, data.encPRFOracle, data.hashOracle⟩
          retained.val.2.2.1.1 retained.val.2.2.1.2.value rows selected.1.1 source data.inputMacKey
          (sharedFixedTranscriptRecords selected.2.2)) (Classical.propDecidable _)

/-- The actual public prefix has the same source-oracle state as the retained observer. -/
theorem sharedMaskSource_prefix [FieldCertificate] [GroupCertificate] (retained : SharedMaskRetainedTape) (sample : PublicSample) :
    runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter (publicMaskTable sample) auxiliary)
      (sharedInitialSourceOracle retained.val.2.2.2) =
    sharedRetainedCoinPrefix adversary parameter auxiliary
      (Shared.restrictOracle retained.val.2.2.2.fixedKeyOracle,
        retained.val.2.2.2.encPRFOracle, retained.val.2.2.2.hashOracle) retained.val.2.2.1.1 sample := rfl

/-- The source split keeps the complete guard after the adaptive input choice. -/
theorem sharedMaskSourceBadObserver_public [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape) :
    (PMF.uniformOfFintype CircuitMaskSample).bind
      (sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained) =
    (PMF.uniformOfFintype PublicSample).bind fun sample =>
      let data := retained.val.2.2.2
      let rows := retainedSourceRows scalar retained.val
      (sharedRetainedCoinPrefix adversary parameter auxiliary
        (Shared.restrictOracle data.fixedKeyOracle, data.encPRFOracle, data.hashOracle)
        retained.val.2.2.1.1 sample).map fun selected =>
          @decide (sharedSourcePrefixBad ⟨data.fixedKeyOracle, data.encPRFOracle, data.hashOracle⟩
            retained.val.2.2.1.1 retained.val.2.2.1.2.value rows selected.1.1
            (circuitMaskSampleSplit retained.val.2.2.1.1 retained.val.2.2.1.2.value rows selected.1.1 sample).2
            data.inputMacKey (sharedFixedTranscriptRecords selected.2.2)) (Classical.propDecidable _) := by
  let choose := fun table => (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) (sharedInitialSourceOracle retained.val.2.2.2)).map
      fun selected => (selected.1.1, selected)
  have law := adaptiveRetainedSource_observation_eq retained.val.2.2.1.1 retained.val.2.2.1.2.value
    (retainedSourceRows scalar retained.val) (rowsForOutputKeysSparse _ _) choose
    (fun selected source => PMF.pure (@decide
      (sharedSourcePrefixBad
        ⟨retained.val.2.2.2.fixedKeyOracle, retained.val.2.2.2.encPRFOracle, retained.val.2.2.2.hashOracle⟩
        retained.val.2.2.1.1 retained.val.2.2.1.2.value (retainedSourceRows scalar retained.val)
        selected.1 source retained.val.2.2.2.inputMacKey (sharedFixedTranscriptRecords selected.2.2.2))
      (Classical.propDecidable _)))
  simp only [choose, PMF.bind_map, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def,
    sharedMaskSource_prefix adversary parameter auxiliary retained] at law
  exact law

/-- The exact independent shared mask source retains the full prefix guard. -/
def sharedGoodMaskSourceBad [FieldCertificate] [GroupCertificate] (scalar : ScalarField) : PMF Bool :=
  (PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
    (PMF.uniformOfFintype CircuitMaskSample).bind
      (sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained)

/-- The actual source failure is contained in the two checked collision flags. -/
theorem sharedMaskSourceBadObserver_flags [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape) :
    ((PMF.uniformOfFintype CircuitMaskSample).bind
      (sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained)).toOuterMeasure {flag | flag = true} ≤
    ((PMF.uniformOfFintype PublicSample).bind fun sample =>
      let split := sharedRetainedSimulatorSourceEquiv (retained, sample)
      sharedRetainedCoinFlags adversary parameter auxiliary (retainedSourceRows scalar retained.val)
        retained.val.2.2.1.2.value split.2.1 split.2.2).toOuterMeasure
          {flags | flags.1 = true ∨ flags.2 = true} := by
  rw [sharedMaskSourceBadObserver_public]
  simp only [PMF.toOuterMeasure_bind_apply]
  apply ENNReal.tsum_le_tsum
  intro sample
  apply mul_le_mul_right
  simp only [sharedRetainedCoinFlags, sharedRetainedSimulatorSourceEquiv, Equiv.coe_fn_mk,
    PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq, decide_eq_true_eq]
  rw [retained.property]
  apply MeasureTheory.measure_mono
  intro selected bad
  by_contra neither
  simp only [Set.mem_setOf_eq, Set.mem_preimage, decide_eq_true_eq, not_or] at neither
  simp only [Set.mem_setOf_eq, Set.mem_preimage, decide_eq_true_eq] at bad
  exact (sharedSourcePrefixBad_split_false
    ⟨retained.val.2.2.2.fixedKeyOracle, retained.val.2.2.2.encPRFOracle, retained.val.2.2.2.hashOracle⟩
    retained.val.2.2.1.1 retained.val.2.2.1.2.value (retainedSourceRows scalar retained.val)
    (rowsForOutputKeysSparse _ _) selected.1.1 sample retained.val.2.2.2.inputMacKey
    (sharedFixedTranscriptRecords selected.2.2)
    (fun good => neither.1 (decide_eq_true_eq.mpr good))
    (fun good => neither.2 (decide_eq_true_eq.mpr good))) bad

/-- The complete independent shared mask source has the checked joint collision bound. -/
theorem sharedGoodMaskSourceBad_mass_le [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    (sharedGoodMaskSourceBad adversary parameter auxiliary scalar).toOuterMeasure {flag | flag = true} ≤
      (169786660680 / 1000) / (2 : ENNReal) ^ 128 +
        (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  apply le_trans _ (sharedConcreteRetainedFlags_mass_le adversary parameter auxiliary scalar)
  unfold sharedGoodMaskSourceBad sharedConcreteRetainedFlags
  rw [uniform_product_bind]
  simp only [PMF.toOuterMeasure_bind_apply]
  apply ENNReal.tsum_le_tsum
  intro retained
  apply mul_le_mul_right
  simpa only [PMF.toOuterMeasure_bind_apply] using
    sharedMaskSourceBadObserver_flags adversary parameter auxiliary scalar retained

end
end Kriterion.ArgoMAC.Security
