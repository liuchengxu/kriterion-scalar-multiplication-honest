import Proof.Privacy.Distribution.SharedMaskSourceDistribution
import Proof.Privacy.Distribution.SharedAdaptiveGateMask
import Proof.Privacy.Distribution.SharedHashRounding

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype bitAdaptorTableFintype
  circuitMaskSampleFintype instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
  instNonemptyPublicSample_2

/-- The ideal gate source retains the actual shared oracle constraint. -/
def actualSharedIdealGateSourceRun [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype SharedOutputRowSource).bind fun source =>
    (PMF.uniformOfFintype PublicSample).bind fun sample =>
      (choose (publicMaskTable sample) (outputSourceOracleRest source.val.2.2)).bind fun selected =>
        observe (publicMaskTable sample) selected
          (retargetGateView sample selected.1 (idealSelectedOutput scalar selected.1 source.val)
            source.val.2.2) (outputSourceOracleRest source.val.2.2)

/-- The exact mask source reaches the ideal shared output with the point-offset error. -/
theorem actualSharedGateSource_ideal_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation) (event : Set Observation) :
    |((actualSharedIdealGateSourceRun scalar choose observe).toOuterMeasure event).toReal -
      (((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedGateSourceRun scalar (maskRetainedTape randomness.val)
              (sharedCircuitMaskSample randomness.val source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (2 : ℝ) ^ (-240 : ℤ) := by
  have sourceLaw := actualSharedMaskSource_observation_eq witness parameter
    (fun retained source => retainedGateSourceRun scalar retained.val source choose observe)
  simp only [sharedMaskRetainedTape] at sourceLaw
  simp_rw [retainedGateSourceRun_actual scalar] at sourceLaw
  rw [sourceLaw]
  exact sharedAdaptiveGateMaskOutput_observation_bound scalar witness parameter
    (fun table rest => choose table (outputSourceOracleRest rest))
    (fun table selected view rest => observe table selected view (outputSourceOracleRest rest)) event

/-- The full source uses the actual shared tape and explicit incomplete-fiber fallback. -/
def actualSharedFullGateSource [FieldCertificate] [GroupCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    PMF Observation :=
  (uniformRandomTape Shared.Randomness witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun source =>
      fullGateSourceRun scalar (maskRetainedTape randomness.val)
        (source.1, sharedCircuitHashRest randomness.val source.2) choose observe fallback

/-- Hash rounding preserves the retained three-slot tape. -/
theorem actualSharedFullGateSource_rounding_bound [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((actualSharedFullGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      (((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
        (PMF.uniformOfFintype
          ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
            retainedGateSourceRun scalar (maskRetainedTape randomness.val)
              (sharedCircuitMaskSample randomness.val source.1 source.2) choose observe)).toOuterMeasure
                event).toReal| ≤ (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have full := actualSharedHashSource_observation_eq witness parameter
    (fun retained source => fullGateSourceRun scalar retained.val source choose observe fallback)
  have good := actualSharedHashSource_observation_eq witness parameter
    (fun retained source => retainedGateSourceRun scalar retained.val
      (circuitMaskHashSplitEquiv.symm source) choose observe)
  have bound := sharedRetainedHashRounding_observation_bound
    (PMF.uniformOfFintype SharedMaskRetainedTape)
    (fun retained source => fullGateSourceRun scalar retained.val source choose observe fallback) event
  simp_rw [fullGateSourceRun_good_pair] at bound
  change actualSharedFullGateSource scalar witness parameter choose observe fallback = _ at full
  rw [full]
  simp only [sharedMaskRetainedTape] at good
  simp only [sharedCircuitMaskSample]
  rw [good]
  exact bound

/-- The complete shared source reaches the ideal gate source with both entrance errors. -/
theorem actualSharedGateSource_observation_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux Observation : Type*}
    (scalar : ScalarField) (witness : Shared.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Aux))
    (observe : Pipeline.Table → (AffineInput × Aux) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (event : Set Observation) :
    |((actualSharedFullGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal -
      ((actualSharedIdealGateSourceRun scalar choose observe).toOuterMeasure event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) := by
  have rounding := actualSharedFullGateSource_rounding_bound scalar witness parameter choose observe fallback event
  have output := actualSharedGateSource_ideal_observation_bound scalar witness parameter choose observe event
  have triangle := abs_sub_le
    ((actualSharedFullGateSource scalar witness parameter choose observe fallback).toOuterMeasure event).toReal
    ((((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          retainedGateSourceRun scalar (maskRetainedTape randomness.val)
            (sharedCircuitMaskSample randomness.val source.1 source.2) choose observe)).toOuterMeasure event).toReal)
    ((actualSharedIdealGateSourceRun scalar choose observe).toOuterMeasure event).toReal
  rw [abs_sub_comm ((actualSharedIdealGateSourceRun scalar choose observe).toOuterMeasure event).toReal] at output
  exact triangle.trans (add_le_add rounding output)

end
end Kriterion.ArgoMAC.Security
