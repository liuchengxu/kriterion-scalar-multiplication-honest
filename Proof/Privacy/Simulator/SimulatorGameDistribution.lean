import Proof.Privacy.Transcript.AdaptiveGameRatio
import Proof.Privacy.Simulator.SimulatorSourceDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

local instance : Nonempty SimulatorCoin := ⟨defaultSimulatorCoin⟩

/-- The public oracle changes only the oracle field of the circuit state. -/
theorem circuitTranscriptFinalState_frame (state : CircuitSimulatorState)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    transcriptFinalState circuitSimulatorOracleHandler state history =
      {state with oracle := (transcriptFinalState circuitSimulatorOracleHandler state history).oracle} := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      simpa only [transcriptFinalState, circuitSimulatorOracleHandler] using
        inductionHypothesis (circuitSimulatorOracleHandler entry.1 state).2

/-- The selected state keeps the original hidden requests and label key. -/
theorem circuitRunTranscript_frame {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : CircuitSimulatorState)
    (output : Result × CircuitSimulatorState × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (runOracleProgramWithTranscript circuitSimulatorOracleHandler program state).support) :
    output.2.1 = {state with oracle := output.2.1.oracle} := by
  rw [runTranscript_finalState circuitSimulatorOracleHandler program state output member]
  exact circuitTranscriptFinalState_frame state output.2.2

/-- The oracle projection keeps every answer and every transcript record. -/
theorem circuitRunTranscript_oracle {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : CircuitSimulatorState) :
    (runOracleProgramWithTranscript circuitSimulatorOracleHandler program state).map
      (fun output => (output.1, output.2.1.oracle, output.2.2)) =
        runOracleProgramWithTranscript idealOracleHandler program state.oracle := by
  induction program generalizing state with
  | pure distribution =>
      simp only [runOracleProgramWithTranscript_pure, PMF.map_comp, Function.comp_def]
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_query, PMF.map_comp, Function.comp_def]
      have law := congrArg (fun distribution => distribution.map (fun output =>
        (output.1, output.2.1, ⟨request, (idealOracleHandler request state.oracle).1⟩ :: output.2.2)))
        (inductionHypothesis (idealOracleHandler request state.oracle).1
          (circuitSimulatorOracleHandler request state).2)
      simpa only [PMF.map_comp, Function.comp_def, circuitSimulatorOracleHandler] using law
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.map_bind]
      apply congrArg distribution.bind
      funext value
      exact inductionHypothesis value state

/-- The oracle run lifts back to the complete circuit state without changing its frame. -/
theorem circuitRunTranscript_lift {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : CircuitSimulatorState) :
    runOracleProgramWithTranscript circuitSimulatorOracleHandler program state =
      (runOracleProgramWithTranscript idealOracleHandler program state.oracle).map (fun output =>
        (output.1, {state with oracle := output.2.1}, output.2.2)) := by
  classical
  have law := congrArg (fun distribution => distribution.map (fun output =>
    (output.1, {state with oracle := output.2.1}, output.2.2))) (circuitRunTranscript_oracle program state)
  simp only [PMF.map_comp, Function.comp_def] at law
  rw [← law]
  symm
  conv_rhs => rw [← PMF.map_id (runOracleProgramWithTranscript circuitSimulatorOracleHandler program state)]
  ext value
  simp only [PMF.map_apply]
  apply tsum_congr
  intro output
  by_cases member : output ∈ (runOracleProgramWithTranscript circuitSimulatorOracleHandler program state).support
  · have frame := circuitRunTranscript_frame program state output member
    have same : (output.1, {state with oracle := output.2.1.oracle}, output.2.2) = output :=
      Prod.ext rfl (Prod.ext frame.symm rfl)
    simp only [same, id_eq]
    split_ifs <;> rfl
  · have zero : (runOracleProgramWithTranscript circuitSimulatorOracleHandler program state) output = 0 := by
      rwa [PMF.apply_eq_zero_iff]
    simp [zero]

/-- Both adaptive phases retain their exact laws after the circuit-frame projection. -/
theorem circuitTwoPhaseTranscript_oracle {First Labels Second : Type}
    {firstBudget secondBudget : Nat}
    (choose : OracleProgram Garbling.oracleSpec First firstBudget)
    (encode : CircuitSimulatorState → First → PMF (Labels × CircuitSimulatorState))
    (decide : First → Labels → OracleProgram Garbling.oracleSpec Second secondBudget)
    (state : CircuitSimulatorState) :
    twoPhaseTranscript circuitSimulatorOracleHandler choose encode decide state =
      twoPhaseTranscript idealOracleHandler choose
        (fun oracle selected => (encode {state with oracle} selected).map
          (fun encoded => (encoded.1, encoded.2.oracle))) decide state.oracle := by
  simp only [twoPhaseTranscript, circuitRunTranscript_lift, PMF.bind_map,
    PMF.map_comp, Function.comp_def]

/-- This kernel states both actual online programming branches. -/
def simulatorOnlineSource [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Option Point) :
    PMF (Garbling.Labels × CircuitSimulatorState) :=
  match output with
  | none =>
      let schedule := (state.selectedCurve input).schedule input (state.labels input).inputMac
      PMF.pure (state.labels input, {state with oracle := programGateSchedule state.oracle schedule})
  | some point =>
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun online =>
          (state.labels input, state.programForOutput input point (Vector.ofFn online.1) online.2)

/-- The online source equals the actual simulator encoding distribution. -/
theorem simulatorOnlineSource_eq [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Option Point) :
    simulatorOnlineSource state input output =
      concreteCircuitSimulator.simulateEncode state input output := by
  cases output <;> rfl

/-- This operation programs exactly the requests retained in a selected source view. -/
def programSelectedGateView (state : SimulatorState) (input : AffineInput)
    (inputMac : InputMac) (view : CurveGateRequest × Option PointGateRequests) : SimulatorState :=
  programGateSchedule state (match view.2 with
    | none => view.1.schedule input inputMac
    | some points => linkedPipelineGateSchedule state view.1 points input inputMac)

/-- The online simulator uses this exact selected request view. -/
theorem simulatorOnlineSource_oracle [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Option Point) :
    (simulatorOnlineSource state input output).map (fun encoded => (encoded.1, encoded.2.oracle)) =
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map (fun online =>
          (state.labels input, programSelectedGateView state.oracle input (state.labels input).inputMac
            (state.selectedCurve input, output.map fun point =>
              state.selectedPoints input point (Vector.ofFn online.1) online.2))) := by
  cases output with
  | none =>
      simp only [simulatorOnlineSource, PMF.pure_map, Option.map_none, programSelectedGateView]
      exact (PMF.map_const _ _).symm
  | some point =>
      simp only [simulatorOnlineSource, PMF.map_comp, Function.comp_def, Option.map_some,
        programSelectedGateView, CircuitSimulatorState.programForOutput,
        CircuitSimulatorState.selectedSchedule]

/-- This transcript exposes the exact offline coin and online source. -/
def simulatorCoinTranscript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :=
  sampledTwoPhaseTranscript circuitSimulatorOracleHandler
    (PMF.uniformOfFintype SimulatorCoin) (fun coin => coin.state.table) SimulatorCoin.state
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun _ state selected => simulatorOnlineSource state selected.1
      (checkedScalarMultiplication scalar.value selected.1))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)

/-- The coin transcript is the concrete ideal endpoint with adversary state. -/
theorem simulatorCoinTranscript_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    simulatorCoinTranscript adversary parameter scalar auxiliary =
      idealAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary := by
  simp only [simulatorCoinTranscript, idealAdaptiveTranscriptWithState, sampledTwoPhaseTranscript,
    concreteCircuitSimulator, circuitSimulator, simulatorStateTape, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  rfl

/-- This transcript retains only the oracle state between the actual simulator phases. -/
def simulatorOracleCoinTranscript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :=
  sampledTwoPhaseTranscript idealOracleHandler
    (PMF.uniformOfFintype SimulatorCoin) (fun coin => coin.state.table) (fun coin => coin.state.oracle)
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun coin state selected =>
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun online =>
          (coin.state.labels selected.1,
            programSelectedGateView state selected.1 (coin.state.labels selected.1).inputMac
              (coin.state.selectedCurve selected.1,
                (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                  coin.state.selectedPoints selected.1 point (Vector.ofFn online.1) online.2)))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)

/-- The oracle transcript removes no public information from the simulator coin transcript. -/
theorem simulatorCoinTranscript_eq_oracle [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    simulatorCoinTranscript adversary parameter scalar auxiliary =
      simulatorOracleCoinTranscript adversary parameter scalar auxiliary := by
  simp only [simulatorCoinTranscript, simulatorOracleCoinTranscript, sampledTwoPhaseTranscript,
    circuitTwoPhaseTranscript_oracle, simulatorOnlineSource_oracle,
    CircuitSimulatorState.labels, CircuitSimulatorState.selectedCurve,
    CircuitSimulatorState.selectedPoints]

end

end Kriterion.ArgoMAC.Security
