import Proof.Privacy.Source.SharedIdealGateCoin
import Proof.Privacy.Source.SharedSimulatorSourceDistribution
import Proof.Privacy.Source.SharedRealEndpointPhaseMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

abbrev SharedFullGateTranscript (State : Type*) :=
  Pipeline.Table × (AffineInput × State) × List (Sigma sharedRealOracleSpec.Answer) ×
    Garbling.Labels × Bool × List (Sigma sharedRealOracleSpec.Answer)

/-- The source state reads the actual three shared permutations. -/
def sharedInitialSourceOracle (data : GarblingOracleData) : Shared.Simulator.OracleState := {
  fixedOracle := Shared.restrictOracle data.fixedKeyOracle
  encOracle := data.encPRFOracle
  hashOracle := data.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false
}

/-- The selected source view uses the exact shared simulator program. -/
def sharedProgramSelectedGateView (state : Shared.Simulator.OracleState) (input : AffineInput)
    (inputMac : InputMac) (view : SelectedGateView) : Shared.Simulator.OracleState :=
  Shared.Simulator.program state (match view.2 with
    | none => view.1.schedule input inputMac
    | some points => linkedPipelineGateSchedule state view.1 points input inputMac)

/-- The input kernel retains the actual shared prefix and its final state. -/
def sharedGateSourceChoose {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) :
    PMF (AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer))) :=
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) (sharedInitialSourceOracle data)).map fun selected =>
      (selected.1.1, selected.1.2, selected.2.1, selected.2.2)

/-- The continuation programs the shared gate view before the second adaptive phase. -/
def sharedGateSourceObserve {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData) : PMF (SharedFullGateTranscript adversary.State) :=
  let labels := sourceInputLabels data selected.1
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.decide parameter table labels auxiliary selected.2.1)
    (sharedProgramSelectedGateView selected.2.2.1 selected.1 labels.inputMac view)).map fun decided =>
      (table, (selected.1, selected.2.1), selected.2.2.2, labels, decided.1, decided.2.2)

/-- The online shared simulator has the exact selected-view distribution. -/
theorem sharedSimulatorEncode_oracle [FieldCertificate] [GroupCertificate]
    (state : Shared.Simulator.State) (input : AffineInput) (output : Option Point) :
    (Shared.Simulator.simulator.simulateEncode state input output).map
      (fun encoded => (encoded.1, encoded.2.oracle)) =
      (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map (fun online =>
          (state.labels input, sharedProgramSelectedGateView state.oracle input (state.labels input).inputMac
            (state.selectedCurve input, output.map fun point =>
              state.selectedPoints input point (Vector.ofFn online.1) online.2))) := by
  cases output with
  | none =>
      simp only [Shared.Simulator.simulator, PMF.pure_map, Option.map_none, sharedProgramSelectedGateView]
      exact (PMF.map_const _ _).symm
  | some point =>
      simp only [Shared.Simulator.simulator, PMF.map_comp, Function.comp_def, Option.map_some,
        sharedProgramSelectedGateView, CircuitSimulatorState.selectedSchedule]

/-- The actual ideal transcript separates the private frame from both shared oracle phases. -/
theorem sharedIdealTranscript_oracle [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology
      Shared.Simulator.simulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary =
      sampledTwoPhaseTranscript idealOracleHandler (Shared.Simulator.tape parameter (Garbling.topology scalar))
        CircuitSimulatorState.table (fun state => state.oracle)
        (fun table => adversary.chooseInput parameter table auxiliary)
        (fun state oracle selected =>
          (PMF.uniformOfFintype ((Fin 90 → Point) ×
            (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun online =>
              (state.labels selected.1,
                sharedProgramSelectedGateView oracle selected.1 (state.labels selected.1).inputMac
                  (state.selectedCurve selected.1,
                    (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                      state.selectedPoints selected.1 point (Vector.ofFn online.1) online.2)))
        (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2) := by
  have offline : Shared.Simulator.simulator.simulateGarble parameter (Garbling.topology scalar) =
      (Shared.Simulator.tape parameter (Garbling.topology scalar)).map (fun state => (state.table, state)) := rfl
  simp only [idealAdaptiveTranscriptWithState, offline, sampledTwoPhaseTranscript, PMF.bind_map, Function.comp_def]
  apply congrArg ((Shared.Simulator.tape parameter (Garbling.topology scalar)).bind)
  funext state
  rw [sharedCircuitTwoPhaseTranscript_oracle]
  simp_rw [sharedSimulatorEncode_oracle]
  rfl

end
end Kriterion.ArgoMAC.Security
