import Proof.Privacy.Source.Invalid.SharedInvalidBadMass
import Proof.Privacy.Source.Invalid.SharedCurveSupportedRatio
import Proof.Privacy.Source.Valid.SharedPipelineSupportedRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble

/-- This source retains the actual shared prefix and its complete continuation. -/
def sharedCombinedSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :=
  (sharedFullGatePrefixSamples scalar witness parameter
    (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).bind fun coin =>
      (sharedFullGatePrefixKernel scalar
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback coin).map (Prod.mk coin)

/-- This guard pays the shared prefix failure once and adds only the invalid hidden-bridge event. -/
def sharedCombinedBad [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (coin : (Shared.Randomness × FullCircuitSource ×
      (AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))) ×
        SharedFullGateTranscript State) : Prop :=
  sharedFullPipelinePrefixBad scalar coin.1 ∨
    sharedFullInvalidHashHit (coin.1.1, coin.1.2.1, coin.2)

/-- Hiding the extra prefix state gives the exact full transcript source. -/
theorem sharedCombinedSource_full [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).map
      (fun coin => (coin.1.1, coin.1.2.1, coin.2)) =
      sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback := by
  rw [sharedFullGateTranscriptSamples_prefix]
  simp only [sharedCombinedSource, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- Hiding the complete source gives the exact full-source experiment. -/
theorem sharedCombinedSource_project [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).bind
      (fun coin => PMF.pure coin.2) =
      actualSharedFullGateSource scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback := by
  have full := congrArg (fun source => source.bind (fun coin => PMF.pure coin.2.2))
    (sharedCombinedSource_full adversary parameter auxiliary scalar witness fallback)
  rw [PMF.bind_map, sharedFullGateTranscriptSamples_project] at full
  exact full

private theorem recordedGood {Source Output : Type*} (samples : PMF Source) (kernel : Source → PMF Output)
    (bad : Set (Source × Output)) (output : Output) :
    sourceGoodMass (samples.bind fun source => (kernel source).map (Prod.mk source))
      (fun coin => PMF.pure coin.2) bad output =
      ∑' source, samples source * if (source, output) ∈ bad then 0 else kernel source output := by
  simp only [sourceGoodMass_bind, sourceGoodMass_map]
  apply tsum_congr
  intro source
  congr 1
  rw [sourceGoodMass, tsum_eq_single output]
  · simp only [Set.mem_preimage, PMF.pure_apply_self]
    split <;> simp_all only [mul_zero, mul_one]
  · intro other different
    simp [PMF.pure_apply, Ne.symm different]

private theorem goodMass_le {Source Output : Type*} (samples : PMF Source) (kernel : Source → PMF Output)
    (first second : Set Source) (output : Output)
    (included : ∀ source ∈ samples.support, output ∈ (kernel source).support → source ∈ second → source ∈ first) :
    sourceGoodMass samples kernel first output ≤ sourceGoodMass samples kernel second output := by
  unfold sourceGoodMass
  apply ENNReal.tsum_le_tsum
  intro source
  by_cases sourceZero : samples source = 0
  · simp only [sourceZero, zero_mul, le_refl]
  by_cases outputZero : kernel source output = 0
  · simp only [outputZero, ite_self, mul_zero, le_refl]
  by_cases bad : source ∈ second
  · simp only [if_pos bad, if_pos (included source sourceZero outputZero bad), mul_zero, le_refl]
  · rw [if_neg bad]
    apply mul_le_mul_right
    split <;> simp only [zero_le, le_refl]

/-- The combined good mass stays below the original good prefix mass. -/
theorem sharedCombinedGood_prefix_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State) :
    sourceGoodMass (sharedCombinedSource adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.2) {coin | sharedCombinedBad scalar coin} output ≤
      sourceGoodMass (sharedFullGatePrefixSamples scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2))
        (sharedFullGatePrefixKernel scalar
          (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
          fallback) {coin | sharedFullPipelinePrefixBad scalar coin} output := by
  apply le_trans (goodMass_le
    (sharedCombinedSource adversary parameter auxiliary scalar witness fallback)
    (fun coin => PMF.pure coin.2) {coin | sharedCombinedBad scalar coin}
    {coin | sharedFullPipelinePrefixBad scalar coin.1} output (fun _ _ _ bad => Or.inl bad))
  rw [sharedCombinedSource, recordedGood]
  exact le_rfl

/-- At invalid outputs, the combined good mass stays below the curve good mass. -/
theorem sharedCombinedGood_curve_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (output : SharedFullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1) :
    sourceGoodMass (sharedCombinedSource adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.2) {coin | sharedCombinedBad scalar coin} output ≤
      sourceGoodMass (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback)
        (fun coin => PMF.pure coin.2.2) {coin | sharedFullCurveBad scalar coin} output := by
  rw [← sharedCombinedSource_full adversary parameter auxiliary scalar witness fallback, sourceGoodMass_map]
  apply goodMass_le
  intro coin supported outputMember bad
  have same : output = coin.2 := by simpa only [PMF.mem_support_pure_iff] using outputMember
  subst output
  obtain ⟨prior, priorMember, mapped⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨result, resultMember, same⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
  cases same
  exact sharedInvalidCurveBad_kernel adversary parameter auxiliary scalar prior fallback result resultMember invalid bad

/-- The combined guard pays exactly one prefix failure and one complete invalid hash event. -/
theorem sharedCombinedBad_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | sharedCombinedBad scalar coin} ≤
      (sharedFullGatePrefixSamples scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {coin | sharedFullPipelinePrefixBad scalar coin} +
      (sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback).toOuterMeasure
        {coin | sharedFullInvalidHashHit coin} := by
  have first : (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).map Prod.fst =
      sharedFullGatePrefixSamples scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2) := by
    simp only [sharedCombinedSource, PMF.map_bind, PMF.map_comp, Function.comp_def]
    trans (sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).bind PMF.pure
    · apply congrArg (sharedFullGatePrefixSamples scalar witness parameter _).bind
      funext coin
      exact PMF.map_const _ _
    · exact PMF.bind_pure _
  apply (MeasureTheory.measure_union_le
    (μ := (sharedCombinedSource adversary parameter auxiliary scalar witness fallback).toOuterMeasure)
    (Prod.fst ⁻¹' {coin | sharedFullPipelinePrefixBad scalar coin})
    ((fun coin => (coin.1.1, coin.1.2.1, coin.2)) ⁻¹' {coin | sharedFullInvalidHashHit coin})).trans_eq
  rw [← PMF.toOuterMeasure_map_apply, first, ← PMF.toOuterMeasure_map_apply, sharedCombinedSource_full]

end
end Kriterion.ArgoMAC.Security
