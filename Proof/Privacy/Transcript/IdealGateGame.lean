import Proof.Privacy.Simulator.SimulatorGameDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩
local instance : Nonempty NonZeroBase := ⟨(Seed.randomness 0).curveMask⟩
local instance : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance : Nonempty SourceOracleRest :=
  ⟨(((Seed.randomness 0).bridgeKey, (Seed.randomness 0).curveMask),
    ⟨(Seed.randomness 0).fixedKeyOracle, (Seed.randomness 0).inputMacKey,
      (Seed.randomness 0).encPRFOracle, (Seed.randomness 0).hashOracle⟩)⟩

/-- This source state contains the actual initial public oracle families. -/
def initialSourceOracle (data : GarblingOracleData) : SimulatorState := {
  fixedOracle := data.fixedKeyOracle
  encOracle := data.encPRFOracle
  hashOracle := data.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false
}

/-- This source encoding uses the actual input MAC key. -/
def sourceInputLabels (data : GarblingOracleData) (input : AffineInput) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := data.inputMacKey.encodeAffine input
}

/-- This input choice retains the full prefix and its final oracle state. -/
def gateSourceChoose {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) :
    PMF (AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) :=
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) (initialSourceOracle data)).map fun selected =>
      (selected.1.1, selected.1.2, selected.2.1, selected.2.2)

/-- This continuation programs the selected source requests before the second phase. -/
def gateSourceObserve {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData) :=
  let labels := sourceInputLabels data selected.1
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.decide parameter table labels auxiliary selected.2.1)
    (programSelectedGateView selected.2.2.1 selected.1 labels.inputMac view)).map fun decided =>
      (table, (selected.1, selected.2.1), selected.2.2.2, labels, decided.1, decided.2.2)

/-- The unused source mask does not change the offline coin distribution. -/
theorem map_uniform_sourceSimulatorCoin :
    (PMF.uniformOfFintype (SourceOracleRest × PublicSample)).map
      (fun source => (simulatorSourceEquiv source).1) = PMF.uniformOfFintype SimulatorCoin := by
  have law := congrArg (fun distribution => distribution.map Prod.fst) map_uniform_simulatorSource
  simpa only [PMF.map_comp, Function.comp_def, map_uniform_prod_fst] using law

/-- The concrete target source is the exact ideal simulator transcript. -/
theorem targetGateSourceRun_eq_simulatorOracleCoinTranscript [FieldCertificate] [GroupCertificate]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    targetGateSourceRun scalar.value (gateSourceChoose adversary parameter auxiliary)
      (gateSourceObserve adversary parameter auxiliary) =
        simulatorOracleCoinTranscript adversary parameter scalar auxiliary := by
  have law := congrArg (fun distribution => sampledTwoPhaseTranscript idealOracleHandler distribution
    (fun coin => coin.state.table) (fun coin => coin.state.oracle)
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun coin state selected =>
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun online =>
          (coin.state.labels selected.1,
            programSelectedGateView state selected.1 (coin.state.labels selected.1).inputMac
              (coin.state.selectedCurve selected.1,
                (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                  coin.state.selectedPoints selected.1 point (Vector.ofFn online.1) online.2)))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2))
      map_uniform_sourceSimulatorCoin
  simpa only [targetGateSourceRun, targetGateObserve, gateSourceChoose, gateSourceObserve,
    simulatorOracleCoinTranscript, sampledTwoPhaseTranscript, twoPhaseTranscript,
    PMF.bind_map, PMF.bind_bind, PMF.map_bind, PMF.map_comp, Function.comp_def,
    simulatorSourceEquiv, Equiv.coe_fn_mk, SimulatorCoin.state, CircuitSimulatorState.table,
    CircuitSimulatorState.labels, CircuitSimulatorState.selectedCurve, CircuitSimulatorState.selectedPoints,
    publicMaskTable, initialSourceOracle, sourceInputLabels, checkedScalarMultiplication,
    Option.map_map] using law

/-- The retained gate source reaches the actual ideal endpoint exactly. -/
theorem idealGateSourceRun_eq_idealTranscript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    idealGateSourceRun scalar.value
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2) =
    idealAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) Garbling.topology
      concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary := by
  exact (idealGateSourceRun_eq_targetGateSourceRun scalar.value
    (gateSourceChoose adversary parameter auxiliary) (gateSourceObserve adversary parameter auxiliary)).trans
    ((targetGateSourceRun_eq_simulatorOracleCoinTranscript adversary parameter scalar auxiliary).trans
      ((simulatorCoinTranscript_eq_oracle adversary parameter scalar auxiliary).symm.trans
        (simulatorCoinTranscript_eq adversary parameter scalar auxiliary)))

/-- The full source reaches the concrete ideal transcript with rounding and output losses. -/
theorem fullGateSource_idealTranscript_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
        Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)))
    (event : Set (Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))) :
    |((fullAdaptiveGateSource scalar.value witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback).toOuterMeasure event).toReal -
      ((idealAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure
          event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) := by
  rw [← idealGateSourceRun_eq_idealTranscript adversary parameter scalar auxiliary]
  exact adaptiveGateSource_observation_bound scalar.value witness parameter
    (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)
    (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
    fallback event

end

end Kriterion.ArgoMAC.Security
