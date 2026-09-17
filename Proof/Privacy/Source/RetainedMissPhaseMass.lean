import Proof.Privacy.Source.PrefixGoodExpansion
import Proof.Privacy.Source.Invalid.InvalidGhostSourceTransport
import Proof.Privacy.Source.GateSourceEndpointMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The missing-query guard separates from the selected-prefix sum. -/
theorem retainedMissWeight_sum [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (samples : PMF (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))))
    (output : FullGateTranscript State) :
    (∑' selected, samples selected * retainedMissWeight scalar observe fallback retained full selected output) =
      if retained.2.2.1.1 ∈ transcriptHashInputs (output.2.2.1 ++ output.2.2.2.2.2) then 0 else
        sourceGoodMass samples
          (fun selected => fullGatePrefixKernel scalar (fun table selected view rest => observe table selected view rest.2)
            fallback (retainedPrefixCoin retained full selected))
          {selected | fullGatePrefixBad (retainedPrefixCoin retained full selected)} output := by
  by_cases hit : retained.2.2.1.1 ∈ transcriptHashInputs (output.2.2.1 ++ output.2.2.2.2.2)
  · simp only [retainedMissWeight, hit, or_true, if_true, mul_zero, tsum_zero]
  · simp only [retainedMissWeight, hit, or_false, if_false, sourceGoodMass, Set.mem_setOf_eq]

/-- The retained prefix mass fixes the raw bad event at the observed input and prefix. -/
theorem retainedPrefixGood_mass [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) :
    sourceGoodMass
      (gateSourceChoose adversary parameter auxiliary
        (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
          (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2)
      (fun selected => fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback (retainedPrefixCoin retained full selected))
      {selected | fullGatePrefixBad (retainedPrefixCoin retained full selected)} output =
    if ¬ FullSourceComplete full.1 ∨ rawSourceBad
      (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
      (decodeFullSource full) output.2.1.1 output.2.2.1 then 0 else
      ((gateSourceChoose adversary parameter auxiliary
        (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
          (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2).bind fun selected =>
        gateSourceObserve adversary parameter auxiliary
          (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) (decodeFullSource full)) selected
          (selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) selected.1 (decodeFullSource full)) selected.1)
          retained.2.2.2) output := by
  by_cases complete : FullSourceComplete full.1
  · simp only [retainedPrefixCoin]; simp_rw [fullGatePrefixBad_reconstructed (State := adversary.State) retained full]
    simp only [complete, not_true_eq_false, false_or]
    simp only [fullGatePrefixKernel_reconstructed scalar _ fallback retained full _ complete]
    exact gateSourceGood_mass adversary parameter auxiliary
      (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2
      (fun input => selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) input (decodeFullSource full)) input)
      (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
      (decodeFullSource full) output
  · simp only [retainedPrefixCoin]; simp_rw [fullGatePrefixBad_reconstructed (State := adversary.State) retained full]
    simp only [complete, not_false_eq_true, true_or, if_true, sourceGoodMass, Set.mem_setOf_eq, mul_zero, tsum_zero]

/-- The table guard lets both adversary factors use the observed table. -/
theorem gateSourcePhases_mass_factor_at {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table observedTable : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    ((gateSourceChoose adversary parameter auxiliary table data).bind fun choice =>
      gateSourceObserve adversary parameter auxiliary table choice (view choice.1) data)
        (observedTable, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter observedTable auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter observedTable labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if table = observedTable ∧
      OracleTranscriptCompatible idealOracleHandler (initialSourceOracle data) before ∧
      sourceInputLabels data selected.1 = labels ∧
      OracleTranscriptCompatible idealOracleHandler
        (programSelectedGateView (transcriptFinalState idealOracleHandler (initialSourceOracle data) before)
          selected.1 (sourceInputLabels data selected.1).inputMac (view selected.1)) after then 1 else 0) := by
  by_cases same : table = observedTable
  · subst observedTable
    simp only [true_and]
    exact gateSourcePhases_mass_factor adversary parameter auxiliary table data view
      referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible
  · simp only [same, false_and, if_false, mul_zero]
    rw [gateSourcePhases_eq, PMF.map_apply]
    simp only [Prod.mk.injEq, Ne.symm same, false_and, if_false, tsum_zero]

private theorem guarded_phase_eq (complete bad hit event : Prop)
    [Decidable complete] [Decidable bad] [Decidable hit] [Decidable event] (factor : ℝ≥0∞) :
    (if hit then 0 else if ¬complete ∨ bad then 0 else factor * (if event then 1 else 0)) =
      factor * (if complete ∧ ¬bad ∧ ¬hit ∧ event then 1 else 0) := by
  by_cases hitCase : hit <;> by_cases completeCase : complete <;> by_cases badCase : bad <;>
    simp [hitCase, completeCase, badCase]

/-- The missing-query source has the two common adversary factors and its exact source event. -/
theorem retainedMissWeight_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table observedTable : Pipeline.Table)
    (tableEq : table = circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
      (retainedSourceRows scalar retained) (decodeFullSource full))
    (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (∑' choice, (gateSourceChoose adversary parameter auxiliary table retained.2.2.2) choice *
      retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback retained full choice
        (observedTable, selected, before, labels, decision, after)) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter observedTable auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter observedTable labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if FullSourceComplete full.1 ∧
      ¬rawSourceBad (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
        (decodeFullSource full) selected.1 before ∧
      retained.2.2.1.1 ∉ transcriptHashInputs (before ++ after) ∧
      table = observedTable ∧
      OracleTranscriptCompatible idealOracleHandler (initialSourceOracle retained.2.2.2) before ∧
      sourceInputLabels retained.2.2.2 selected.1 = labels ∧
      OracleTranscriptCompatible idealOracleHandler
        (programSelectedGateView (transcriptFinalState idealOracleHandler (initialSourceOracle retained.2.2.2) before)
          selected.1 (sourceInputLabels retained.2.2.2 selected.1).inputMac
          (selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) selected.1 (decodeFullSource full)) selected.1)) after
      then 1 else 0) := by
  subst table
  have missing := retainedMissWeight_sum scalar (gateSourceObserve adversary parameter auxiliary) fallback
    retained full
    (gateSourceChoose adversary parameter auxiliary
      (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2)
    (observedTable, selected, before, labels, decision, after)
  rw [retainedPrefixGood_mass adversary parameter auxiliary scalar retained full fallback
    (observedTable, selected, before, labels, decision, after)] at missing
  rw [gateSourcePhases_mass_factor_at adversary parameter auxiliary
    (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
      (retainedSourceRows scalar retained) (decodeFullSource full)) observedTable retained.2.2.2
    (fun input => selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
      (retainedSourceRows scalar retained) input (decodeFullSource full)) input)
    referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible] at missing
  dsimp only at missing
  exact missing.trans (guarded_phase_eq _ _ _ _ _)

end
end Kriterion.ArgoMAC.Security
