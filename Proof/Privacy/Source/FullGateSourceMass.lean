import Proof.Privacy.Transcript.IdealGateGame
import Proof.Privacy.Source.FullSourceGood
import Proof.Shared.SourceHCoefficient

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instNonemptyCircuitHashRest_1

/-- This source keeps the random tape, full hash tag, and adaptive input prefix. -/
def fullGatePrefixSamples [FieldCertificate] [GroupCertificate] {Prefix : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix)) :=
  (randomTape witness parameter).bind fun randomness =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun tag =>
      let retained := maskRetainedTape randomness
      let source := decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)
      let table := circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) source
      (choose table retained.2.2).map fun selected => (randomness, tag, selected)

/-- This kernel runs the selected requests or the incomplete-source fallback. -/
def fullGatePrefixKernel [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (sample : Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
      (AffineInput × Prefix)) : PMF Observation :=
  let retained := maskRetainedTape sample.1
  let source := (sample.2.1.1, sharedCircuitHashRest sample.1 sample.2.1.2)
  if FullSourceComplete source.1 then
    let decoded := decodeFullSource source
    let rows := retainedSourceRows scalar retained
    let table := circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value rows decoded
    observe table sample.2.2 (selectedGateView
      (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value rows sample.2.2.1 decoded)
      sample.2.2.1) retained.2.2
  else fallback retained source

/-- The full source factors through the complete adaptive prefix sample. -/
theorem fullGatePrefixSamples_bind [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix))
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView →
      SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    (fullGatePrefixSamples scalar witness parameter choose).bind
      (fullGatePrefixKernel scalar observe fallback) =
        fullAdaptiveGateSource scalar witness parameter choose observe fallback := by
  simp only [fullGatePrefixSamples, fullAdaptiveGateSource, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (randomTape witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype
      ((RawCircuitGate → FullHashLift) × CircuitMaskTables) finite inferInstance)
    exact Subsingleton.elim _ _
  funext tag
  by_cases complete : FullSourceComplete tag.1
  · simp only [fullGatePrefixKernel, fullGateSourceRun, complete, if_true, retainedGateSourceRun]
  · simp only [fullGatePrefixKernel, fullGateSourceRun, complete, if_false, PMF.bind_const]


/-- This predicate rejects incomplete hashes and the actual bad source prefix. -/
def fullGatePrefixBad [FieldCertificate] [GroupCertificate] {State : Type}
    (sample : Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
      (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))) : Prop :=
  let retained := maskRetainedTape sample.1
  let source := (sample.2.1.1, sharedCircuitHashRest sample.1 sample.2.1.2)
  let coin := (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
  ¬ FullSourceComplete source.1 ∨
    rawSourceBad coin (decodeFullSource source) sample.2.2.1 sample.2.2.2.2.2

/-- The prefix bad event is exactly the checked full-source flag. -/
theorem fullGatePrefixBad_map [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness) :
    (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).map
        (fun sample => @decide (fullGatePrefixBad sample) (Classical.propDecidable _)) =
      fullRetainedBadSource adversary parameter auxiliary scalar witness := by
  simp only [fullGatePrefixSamples, fullRetainedBadSource, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  apply congrArg (randomTape witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype
      ((RawCircuitGate → FullHashLift) × CircuitMaskTables) finite inferInstance)
    exact Subsingleton.elim _ _
  funext tag
  by_cases complete : FullSourceComplete tag.1
  · simp only [fullRetainedBadObserver, complete, if_true, fullGatePrefixBad, not_true_eq_false,
      false_or, gateSourceChoose, maskSourceBadObserver, PMF.map_comp, Function.comp_def]
    rfl
  · simp only [fullRetainedBadObserver, complete, if_false, fullGatePrefixBad, not_false_eq_true,
      true_or]
    exact PMF.map_const _ _


/-- The exact prefix source pays the checked collision and rounding losses. -/
theorem fullGatePrefixBad_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness) :
    ((fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {sample | fullGatePrefixBad sample}).toReal ≤
      224668080 / (2 : ℝ) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have law := congrArg (fun distribution : PMF Bool =>
    (distribution.toOuterMeasure {flag | flag = true}).toReal)
    (fullGatePrefixBad_map adversary parameter auxiliary scalar witness)
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq, decide_eq_true_eq] at law
  rw [law]
  exact fullRetainedBadSource_mass_le adversary parameter auxiliary scalar witness

/-- The missing good transcript mass equals the checked source loss. -/
theorem fullGatePrefixGood_missing_le [FieldCertificate] [GroupCertificate] {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (observe : Pipeline.Table →
      (AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation) :
    let choose := fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2
    let samples := fullGatePrefixSamples scalar witness parameter choose
    let kernel := fullGatePrefixKernel scalar observe fallback
    (∑' transcript : Observation,
      ((fullAdaptiveGateSource scalar witness parameter choose observe fallback) transcript -
        sourceGoodMass samples kernel {sample | fullGatePrefixBad sample} transcript)).toReal ≤
      224668080 / (2 : ℝ) ^ 128 +
        (182 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  dsimp only
  rw [← fullGatePrefixSamples_bind, sourceGoodMass_missing]
  exact fullGatePrefixBad_mass_le adversary parameter auxiliary scalar witness

end

end Kriterion.ArgoMAC.Security
