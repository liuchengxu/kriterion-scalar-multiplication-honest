import Proof.Privacy.Source.SourceGoodMassExpansion
import Proof.Privacy.Source.FullGateGhostMass
import Proof.Privacy.Source.SourceTranscriptCompatibility

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- A supported transcript fixes any source guard that it determines. -/
theorem sourceGoodMass_guard_eq {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript)
    (bad : Set Source) (transcript : Transcript) (failed : Prop) [Decidable failed]
    (determines : ∀ source, transcript ∈ (kernel source).support → (source ∈ bad ↔ failed)) :
    sourceGoodMass samples kernel bad transcript =
      if failed then 0 else (samples.bind kernel) transcript := by
  have each (source : Source) :
      samples source * (if source ∈ bad then 0 else kernel source transcript) =
        samples source * (if failed then 0 else kernel source transcript) := by
    by_cases zero : kernel source transcript = 0
    · simp [zero]
    · have same := determines source zero
      by_cases badOutcome : failed
      · simp [same.mpr badOutcome, badOutcome]
      · simp [mt same.mp badOutcome, badOutcome]
  unfold sourceGoodMass
  simp_rw [each]
  by_cases badOutcome : failed <;> simp [badOutcome, PMF.bind_apply]

/-- The source continuation fixes the raw bad event at its observed input and prefix. -/
theorem gateSourceGood_mass {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (coin : SimulatorCoin) (source : CircuitMaskSample) (output : FullGateTranscript adversary.State) :
    sourceGoodMass (gateSourceChoose adversary parameter auxiliary table data)
      (fun selected => gateSourceObserve adversary parameter auxiliary table selected (view selected.1) data)
      {selected | rawSourceBad coin source selected.1 selected.2.2.2} output =
    if rawSourceBad coin source output.2.1.1 output.2.2.1 then 0 else
      ((gateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
        gateSourceObserve adversary parameter auxiliary table selected (view selected.1) data) output := by
  apply sourceGoodMass_guard_eq
  intro selected member
  have tag := gateSourceObserve_tag adversary parameter auxiliary table data selected
    (view selected.1) output member
  have input := congrArg (fun value => value.2.1.1) tag
  have history := congrArg (fun value => value.2.2.1) tag
  dsimp only at input history
  rw [input, history]
  rfl

/-- Two source choices preserve the exact mass under their shared map. -/
theorem sourceGoodMass_nested_map {Outer Inner Choice Source Transcript : Type*}
    (outer : PMF Outer) (inner : PMF Inner) (choices : Outer → Inner → PMF Choice)
    (project : Outer → Inner → Choice → Source) (kernel : Source → PMF Transcript)
    (bad : Set Source) (output : Transcript) (samples : PMF Source)
    (samplesEq : samples = outer.bind fun first => inner.bind fun second =>
      (choices first second).map (project first second)) :
    sourceGoodMass samples kernel bad output =
      ∑' first, outer first * ∑' second, inner second *
        sourceGoodMass (choices first second) (fun choice => kernel (project first second choice))
          {choice | bad (project first second choice)} output := by
  rw [samplesEq]
  simp only [sourceGoodMass_bind, sourceGoodMass_map]; rfl

private theorem fullGatePrefixSamples_expansion [FieldCertificate] [GroupCertificate] {Prefix : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix)) :
    fullGatePrefixSamples scalar witness parameter choose =
      (randomTape witness parameter).bind fun randomness =>
        (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)).bind fun tag =>
          (choose (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1 (maskRetainedTape randomness).2.2.1.2.value
            (retainedSourceRows scalar (maskRetainedTape randomness))
            (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) (maskRetainedTape randomness).2.2).map
              (fun selected => (randomness, tag, selected)) := by
  rfl

private theorem fullGatePrefixGood_mass_aux [FieldCertificate] [GroupCertificate]
    {Prefix Observation : Type*} (scalar : ScalarField)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix))
    (kernel : (Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) × (AffineInput × Prefix)) → PMF Observation)
    (bad : Set (Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) × (AffineInput × Prefix)))
    (output : Observation) (samples : PMF (Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) × (AffineInput × Prefix)))
    (tapes : PMF Garbling.Randomness) (tags : PMF ((RawCircuitGate → FullHashLift) × CircuitMaskTables))
    (shared : samples = tapes.bind fun randomness => tags.bind fun tag =>
      (choose (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1 (maskRetainedTape randomness).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape randomness))
        (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) (maskRetainedTape randomness).2.2).map
        (fun selected => (randomness, tag, selected))) :
    sourceGoodMass samples kernel bad output =
    ∑' randomness, tapes randomness * ∑' tag, tags tag *
      sourceGoodMass (choose (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1 (maskRetainedTape randomness).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape randomness))
        (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) (maskRetainedTape randomness).2.2)
        (fun selected => kernel (randomness, tag, selected))
        {selected | bad (randomness, tag, selected)} output := by
  exact sourceGoodMass_nested_map tapes tags
    (fun randomness tag =>
      choose (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1 (maskRetainedTape randomness).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape randomness))
        (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) (maskRetainedTape randomness).2.2)
    (fun randomness tag selected => (randomness, tag, selected)) kernel bad output samples shared

set_option maxRecDepth 2048 in
/-- The full prefix good mass retains every original tape and full tag exactly. -/
theorem fullGatePrefixGood_mass [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField) (witness : Garbling.Randomness) (parameter : Nat)
    (choose : Pipeline.Table → SourceOracleRest → PMF (AffineInput × Prefix))
    (kernel : (Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) × (AffineInput × Prefix)) → PMF Observation)
    (bad : Set (Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) × (AffineInput × Prefix)))
    (output : Observation) :
    sourceGoodMass (fullGatePrefixSamples scalar witness parameter choose) kernel bad output =
    ∑' randomness, (randomTape witness parameter) randomness *
      ∑' tag : ((RawCircuitGate → FullHashLift) × CircuitMaskTables), (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)) tag *
        sourceGoodMass (choose (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1 (maskRetainedTape randomness).2.2.1.2.value
          (retainedSourceRows scalar (maskRetainedTape randomness))
          (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) (maskRetainedTape randomness).2.2)
          (fun selected => kernel (randomness, tag, selected))
          {selected | bad (randomness, tag, selected)} output := by
  exact fullGatePrefixGood_mass_aux scalar choose kernel bad output
    (fullGatePrefixSamples scalar witness parameter choose) (randomTape witness parameter)
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables))
    (fullGatePrefixSamples_expansion scalar witness parameter choose)

/-- A complete prefix component has exactly the observed raw source guard. -/
theorem fullGatePrefixGood_component [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (randomness : Garbling.Randomness) (tag : ((RawCircuitGate → FullHashLift) × CircuitMaskTables))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) (output : FullGateTranscript adversary.State) :
    let retained := maskRetainedTape randomness
    let full := (tag.1, sharedCircuitHashRest randomness tag.2)
    let source := decodeFullSource full
    let rows := retainedSourceRows scalar retained
    let table := circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value rows source
    let coin := (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
    sourceGoodMass (gateSourceChoose adversary parameter auxiliary table retained.2.2.2)
      (fun selected => fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback (randomness, tag, selected))
      {selected | fullGatePrefixBad (randomness, tag, selected)} output =
    if ¬ FullSourceComplete tag.1 ∨ rawSourceBad coin source output.2.1.1 output.2.2.1 then 0 else
      ((gateSourceChoose adversary parameter auxiliary table retained.2.2.2).bind fun selected =>
        gateSourceObserve adversary parameter auxiliary table selected
          (selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
            rows selected.1 source) selected.1) retained.2.2.2) output := by
  dsimp only
  by_cases complete : FullSourceComplete tag.1
  · simp only [fullGatePrefixKernel, fullGatePrefixBad, complete, if_true, not_true_eq_false, false_or]
    exact gateSourceGood_mass adversary parameter auxiliary
      (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1
        (maskRetainedTape randomness).2.2.1.2.value (retainedSourceRows scalar (maskRetainedTape randomness))
        (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)))
      (maskRetainedTape randomness).2.2.2
      (fun input => selectedGateView
        (circuitMaskSampleGarble (maskRetainedTape randomness).2.2.1.1
          (maskRetainedTape randomness).2.2.1.2.value (retainedSourceRows scalar (maskRetainedTape randomness))
          input (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2))) input)
      (simulatorSourceEquiv ((maskRetainedTape randomness).2.2, defaultSimulatorCoin.tableSample)).1
      (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)) output
  · simp only [fullGatePrefixBad, complete, not_false_eq_true, true_or, if_true,
      sourceGoodMass, Set.mem_setOf_eq, mul_zero, tsum_zero]

end

end Kriterion.ArgoMAC.Security
