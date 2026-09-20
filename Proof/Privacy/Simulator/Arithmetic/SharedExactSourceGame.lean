import Proof.Privacy.Simulator.Arithmetic.SharedFiniteSourceDecision
import Proof.Privacy.Simulator.Arithmetic.PublicWire
import Proof.Privacy.Simulator.SharedGameDistribution
import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.Assumptions Security Security.SharedSimulatorMachine GarbledCircuit
noncomputable section

/-- The initial shared source has no transcripts, commitments, or collision flag. -/
def emptySharedMetadata : Metadata := ⟨[], [], [], [], none, false⟩

/-- The private frame uses the exact offline coin and receives its eager oracle from completion. -/
def sharedOfflineFrame (coin : SimulatorSampling.OfflineCoin) : Shared.Simulator.State :=
  Shared.Simulator.initialState coin defaultSharedOracleCoin

/-- A public query program changes only the recording oracle in the private circuit frame. -/
theorem sharedCircuitProgram_oracle {Result : Type} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget) (state : Shared.Simulator.State) :
    program.run circuitSimulatorOracleHandler state =
      (program.run idealOracleHandler state.oracle).map fun result => (result.1, {state with oracle := result.2}) := by
  induction program generalizing state with
  | pure distribution => simp only [OracleProgram.run_pure, PMF.map_comp]; rfl
  | query request next ih => simp only [OracleProgram.run_query, circuitSimulatorOracleHandler, ih]
  | sample distribution next ih => simp only [OracleProgram.run_sample, PMF.map_bind, ih]

/-- Offline private coins commute with the independent shared public oracle coin. -/
theorem sharedTape_coinFirst {Result : Type} (parameter : Nat) (topology : Garbling.Topology)
    (observe : Shared.Simulator.State → PMF Result) :
    (Shared.Simulator.tape parameter topology).bind observe =
      SimulatorSampling.offline.law.bind fun coin =>
        (letI : Nonempty SharedOracleCoin := ⟨defaultSharedOracleCoin⟩
         PMF.uniformOfFintype SharedOracleCoin).bind fun oracles => observe (Shared.Simulator.initialState coin oracles) := by
  simp only [Shared.Simulator.tape, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]

/-- The source passes the complete sampled table to the adaptive input selector. -/
def sharedWireSourceChoose {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin) :=
  adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary

/-- The source passes the exact selected Lamport blocks to the final adaptive program. -/
def sharedWireSourceDecide {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) :=
  adversary.decide parameter (publicSourceTable coin.1) (Lamport.selectedLabels labels.inputMac) auxiliary selected.2

/-- The exact completed source is the existing shared wire simulator's full adaptive game. -/
theorem sharedExactSourceDecision_idealGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    sharedExactSourceDecision sharedOfflineFrame (sharedWireSourceChoose adversary parameter auxiliary)
      Prod.fst (fun selected => Shared.wireCircuit.function scalar selected.1)
      (sharedWireSourceDecide adversary parameter auxiliary) (fun _ => initialSharedOracleSource emptySharedMetadata) =
    idealGame Shared.packedCircuit (fun _ => 8887896) Shared.Simulator.packedWireSimulator
      circuitSimulatorOracleHandler adversary parameter scalar auxiliary := by
  simp only [sharedExactSourceDecision, initialSharedOracleSource_completion, PMF.bind_map, sharedAdaptiveProgram_run,
    sharedWireSourceChoose, sharedWireSourceDecide, PMF.map_bind, Function.comp_def]
  simp only [idealGame, Shared.packedCircuit, Shared.Simulator.packedWireSimulator,
    Shared.Simulator.wireSimulator, GarbledCircuit.mapPublic, Simulator.mapPublic, Simulator.mapLabels,
    Shared.Simulator.simulator,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [sharedTape_coinFirst]
  apply congrArg (PMF.bind SimulatorSampling.offline.law)
  funext coin
  apply congrArg (PMF.bind (letI : Nonempty SharedOracleCoin := ⟨defaultSharedOracleCoin⟩; PMF.uniformOfFintype SharedOracleCoin))
  funext oracles
  simp only [sharedCircuitProgram_oracle, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
