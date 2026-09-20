import Proof.Privacy.Collision.SharedPipelinePrefixBad
import Proof.Privacy.ThreePhasePrivacy

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble retainedFullTable circuitMaskSourceTable
set_option maxRecDepth 2048

variable {Aux : Type}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The full-source observer checks completeness and the exact source prefix in one run. -/
theorem sharedFullRetainedBadObserver_run [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    sharedFullRetainedBadObserver adversary parameter auxiliary scalar retained full =
      (runOracleProgramWithTranscript idealOracleHandler
        (adversary.chooseInput parameter
          (circuitMaskSourceTable retained.val.2.2.1.1 retained.val.2.2.1.2.value
            (retainedSourceRows scalar retained.val) (decodeFullSource full)) auxiliary)
        (sharedInitialSourceOracle retained.val.2.2.2)).map fun selected =>
          @decide (¬ FullSourceComplete full.1 ∨
            sharedSourcePrefixBad
              ⟨retained.val.2.2.2.fixedKeyOracle, retained.val.2.2.2.encPRFOracle, retained.val.2.2.2.hashOracle⟩
              retained.val.2.2.1.1 retained.val.2.2.1.2.value (retainedSourceRows scalar retained.val)
              selected.1.1 (decodeFullSource full) retained.val.2.2.2.inputMacKey
              (sharedFixedTranscriptRecords selected.2.2)) (Classical.propDecidable _) := by
  unfold sharedFullRetainedBadObserver
  by_cases complete : FullSourceComplete full.1
  · simp only [complete, if_true, not_true_eq_false, false_or]
    rfl
  · simp only [complete, if_false, not_false_eq_true, true_or, decide_true]
    exact (PMF.map_const _ _).symm

/-- Every actual prefix component has the same failure flag as the complete source observer. -/
theorem sharedFullPipelinePrefixBad_component [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (tape : Shared.Randomness) (tag : FullCircuitSource) :
    (sharedGateSourceChoose adversary parameter auxiliary
      (circuitMaskSourceTable (maskRetainedTape tape.val).2.2.1.1 (maskRetainedTape tape.val).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape tape.val))
        (decodeFullSource (tag.1, sharedCircuitHashRest tape.val tag.2)))
      (maskRetainedTape tape.val).2.2.2).map
        (fun selected => @decide (sharedFullPipelinePrefixBad scalar (tape, tag, selected)) (Classical.propDecidable _)) =
    sharedFullRetainedBadObserver adversary parameter auxiliary scalar (sharedMaskRetainedTape tape)
      (tag.1, sharedCircuitHashRest tape.val tag.2) := by
  rw [sharedFullRetainedBadObserver_run]
  simp only [sharedGateSourceChoose, PMF.map_comp, Function.comp_def]
  simp only [PMF.map]
  apply ThreePhase.bind_eq_on_support
  intro selected member
  have same := sharedFullPipelinePrefixBad_source scalar tape tag
    (selected.1.1, selected.1.2, selected.2)
    (runOracleProgramWithTranscript_compatible idealOracleHandler _ _ selected member)
  dsimp only [Function.comp_def]
  rw [propext same]
  rfl

/-- The actual shared prefix failure has the exact complete retained source law. -/
theorem sharedFullPipelinePrefixBad_law [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (witness : Shared.Randomness) :
    (sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).map
        (fun sample => @decide (sharedFullPipelinePrefixBad scalar sample) (Classical.propDecidable _)) =
      sharedFullRetainedBadSource adversary parameter auxiliary scalar := by
  simp only [sharedFullGatePrefixSamples, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp_rw [sharedFullPipelinePrefixBad_component adversary parameter auxiliary scalar]
  exact actualSharedHashSource_observation_eq witness parameter
    (sharedFullRetainedBadObserver adversary parameter auxiliary scalar)

/-- The actual complete shared prefix pays the checked collision and hash-rounding losses. -/
theorem sharedFullPipelinePrefixBad_mass_le [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (witness : Shared.Randomness) :
    ((sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {sample | sharedFullPipelinePrefixBad scalar sample}).toReal ≤
      (169786660680 / 1000) / (2 : ℝ) ^ 128 +
        (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have bound := sharedFullRetainedBadSource_mass_le adversary parameter auxiliary scalar
  rw [← sharedFullPipelinePrefixBad_law adversary parameter auxiliary scalar witness,
    PMF.toOuterMeasure_map_apply] at bound
  simpa only [Set.preimage_setOf_eq, decide_eq_true_eq] using bound

end
end Kriterion.ArgoMAC.Security
