import Proof.Privacy.Simulator.SimulatorMachineInitial
import Proof.Privacy.Simulator.SimulatorProtocol

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open Cryptography.Assumptions OperationalOracle
namespace SimulatorMachine
open SimulatorSampling
noncomputable section

/-- The original simulator starts with empty transcripts and no collision. -/
def initialMetadata : Metadata := ⟨[], [], [], [], none, false⟩

/-- This handler interprets external bounded sparse draws. -/
abbrev externalHandler (query : Garbling.OracleQuery) (state : SparseState) :
    PMF (Garbling.OracleAnswer query × SparseState) := (externalDraw query state).distribution

/-- The external joint law applies to every adaptive adversary program. -/
theorem external_adaptive_joint {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : SparseState) :
    (completion state).bind (fun eagerState => program.run idealOracleHandler eagerState) =
      (runSampled externalHandler program state).bind (fun output =>
        (completion output.2).map (fun eagerState => (output.1, eagerState))) :=
  adaptive_joint_law idealOracleHandler externalHandler completion external_step program state

/-- A joint completion law remains exact under every following computation. -/
theorem joint_bind {oracle : OracleSpec} {Result Sparse Eager Output : Type}
    (handler : OracleHandler oracle Eager)
    (sampled : ∀ query, Sparse → PMF (oracle.Answer query × Sparse))
    (kernel : Sparse → PMF Eager)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : Sparse)
    (joint : (kernel state).bind (fun eagerState => program.run handler eagerState) =
      (runSampled sampled program state).bind (fun output =>
        (kernel output.2).map (fun eagerState => (output.1, eagerState))))
    (next : Result × Eager → PMF Output) :
    (kernel state).bind (fun eagerState =>
      (program.run handler eagerState).bind next) =
      (runSampled sampled program state).bind (fun output =>
        (kernel output.2).bind (fun eagerState => next (output.1, eagerState))) := by
  have law := congrArg (fun distribution : PMF (Result × Eager) =>
    distribution.bind next) joint
  simpa only [PMF.bind_bind, PMF.bind_map, Function.comp_def] using law

/-- The circuit handler keeps the private coin while it updates the oracle state. -/
theorem external_private_run {Result : Type} {budget : Nat}
    (coin : OfflineCoin) (program : OracleProgram Garbling.oracleSpec Result budget)
    (oracle : SimulatorState) :
    program.run circuitSimulatorOracleHandler (privateState coin oracle) =
      (program.run idealOracleHandler oracle).map
        (fun output => (output.1, privateState coin output.2)) := by
  induction program generalizing oracle with
  | pure distribution =>
      simp only [OracleProgram.run_pure, PMF.map_comp]
      rfl
  | query request next inductionHypothesis =>
      rw [OracleProgram.run_query, OracleProgram.run_query]; change (next (idealOracleHandler request oracle).1).run circuitSimulatorOracleHandler
        (privateState coin (idealOracleHandler request oracle).2) = _
      exact inductionHypothesis _ _
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run_sample, PMF.map_bind, inductionHypothesis]

/-- The online simulator changes only the oracle field of its private state. -/
theorem simulateEncode_rebuild [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Option Point) :
    (concreteCircuitSimulator.simulateEncode state input output).map
        (fun answer => (answer.1, { state with oracle := answer.2.oracle })) =
      concreteCircuitSimulator.simulateEncode state input output := by
  cases output with
  | none => simp only [concreteCircuitSimulator, circuitSimulator, PMF.pure_map]
  | some point =>
      simp only [concreteCircuitSimulator, circuitSimulator, PMF.map_comp]
      apply congrArg (fun f => (PMF.uniformOfFintype ((Fin 90 → Point) ×
        (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map f)
      funext sample
      simp only [Function.comp_def, CircuitSimulatorState.programForOutput]

/-- The online program preserves the full private simulator state. -/
theorem encodeProgram_full_law [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (oracle : SimulatorState) (input : AffineInput) (output : Option Point) :
    ((encodeProgram coin input output).run handler oracle).map
        (fun answer => (answer.1, privateState coin answer.2)) =
      concreteCircuitSimulator.simulateEncode (privateState coin oracle) input output := by
  rw [encodeProgram_law, PMF.map_comp]
  calc
    _ = (concreteCircuitSimulator.simulateEncode (privateState coin oracle) input output).map
        (fun answer => (answer.1, { privateState coin oracle with oracle := answer.2.oracle })) := by
      congr 1
    _ = _ := simulateEncode_rebuild _ _ _

/-- This continuation runs the three adversary phases against the full eager oracles. -/
def eagerContinuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (coin : OfflineCoin) (oracle : SimulatorState) : PMF Bool :=
  ((adversary.prepare parameter auxiliary).run idealOracleHandler oracle).bind (fun prepared =>
    ((adversary.chooseInput parameter (privateView coin).table auxiliary prepared.1).run
      idealOracleHandler prepared.2).bind (fun selected =>
      ((encodeProgram coin selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)).run handler selected.2).bind
        (fun encoded => ((adversary.decide parameter (privateView coin).table encoded.1 auxiliary selected.1.2).run
          idealOracleHandler encoded.2).map Prod.fst)))

/-- This continuation uses only bounded sparse oracle operations. -/
def sparseContinuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (coin : OfflineCoin) (state : SparseState) : PMF Bool :=
  (runSampled externalHandler (adversary.prepare parameter auxiliary) state).bind (fun prepared =>
    (runSampled externalHandler
      (adversary.chooseInput parameter (privateView coin).table auxiliary prepared.1) prepared.2).bind (fun selected =>
      (runSampled sparseHandler (encodeProgram coin selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)) selected.2).bind
        (fun encoded => (runSampled externalHandler
          (adversary.decide parameter (privateView coin).table encoded.1 auxiliary selected.1.2) encoded.2).map Prod.fst)))

/-- The completion law transports the entire three-phase continuation exactly. -/
theorem continuation_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (coin : OfflineCoin) (state : SparseState) :
    (completion state).bind (eagerContinuation adversary parameter scalar auxiliary coin) =
      sparseContinuation adversary parameter scalar auxiliary coin state := by
  unfold eagerContinuation sparseContinuation
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  congr 1
  funext prepared
  dsimp only
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  congr 1
  funext selected
  dsimp only
  rw [joint_bind handler sparseHandler completion _ _ (sparse_adaptive_joint _ _)]
  congr 1
  funext encoded
  dsimp only
  have last := congrArg (fun distribution : PMF (Bool × SimulatorState) => distribution.map Prod.fst)
    (external_adaptive_joint
      (adversary.decide parameter (privateView coin).table encoded.1 auxiliary selected.1.2) encoded.2)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at last
  have finish (output : Bool × SparseState) :
      (completion output.2).map (fun _ => output.1) = PMF.pure output.1 :=
    PMF.map_const _ _
  simp_rw [finish] at last
  simpa only [PMF.map, Function.comp_def] using last

/-- The operational ideal game samples private coins and uses bounded sparse oracle operations. -/
def operationalIdealGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  offline.law.bind (fun coin => sparseContinuation adversary parameter scalar auxiliary coin (initial initialMetadata))

/-- This eager game uses the same operational program with the original uniform oracle coin. -/
def eagerIdealGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  let : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
  offline.law.bind (fun coin => (PMF.uniformOfFintype SimulatorOracleCoin).bind
    (fun oracles => eagerContinuation adversary parameter scalar auxiliary coin (withOracles initialMetadata oracles)))

/-- Sparse and eager operational experiments have exactly equal decision distributions. -/
theorem operational_eq_eager [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    operationalIdealGame adversary parameter scalar auxiliary = eagerIdealGame adversary parameter scalar auxiliary := by
  unfold operationalIdealGame eagerIdealGame
  congr 1
  funext coin
  rw [← continuation_law, initial_completion, PMF.bind_map]
  rfl

/-- The private table does not depend on the oracle environment. -/
theorem privateState_table (coin : OfflineCoin) (oracle : SimulatorState) :
    (privateState coin oracle).table = (privateView coin).table := rfl

/-- The offline sample splits into the exact private coin and original oracle coin. -/
theorem stateTape_split (parameter : Nat) (topology : Garbling.Topology) :
    let : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
    simulatorStateTape parameter topology =
      (PMF.uniformOfFintype SimulatorOracleCoin).bind (fun oracles =>
        offline.law.map (fun coin => privateState coin (withOracles initialMetadata oracles))) := by
  let : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
  unfold simulatorStateTape
  rw [← offline_with_oracles, PMF.map_bind]
  simp only [PMF.map_comp]
  rfl

/-- The eager operational game equals the original three-phase ideal experiment. -/
theorem eager_eq_original [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    eagerIdealGame adversary parameter scalar auxiliary =
      ThreePhase.idealGame adversary parameter scalar auxiliary := by
  let : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
  unfold ThreePhase.idealGame
  rw [stateTape_split]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  unfold eagerIdealGame
  apply congrArg (PMF.bind offline.law)
  funext coin
  apply congrArg (PMF.bind (PMF.uniformOfFintype SimulatorOracleCoin))
  funext oracles
  simp only [eagerContinuation, external_private_run, PMF.bind_map, Function.comp_def,
    privateState_table]
  simp only [← encodeProgram_full_law, PMF.bind_map, Function.comp_def,
    external_private_run, PMF.map_comp]

/-- The operational simulator has exactly the original ideal decision distribution. -/
theorem operationalIdealGame_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    operationalIdealGame adversary parameter scalar auxiliary =
      ThreePhase.idealGame adversary parameter scalar auxiliary :=
  (operational_eq_eager adversary parameter scalar auxiliary).trans
    (eager_eq_original adversary parameter scalar auxiliary)

/-- The bounded sparse simulator satisfies the original 100-bit three-phase privacy theorem. -/
theorem operationalPrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (operationalIdealGame adversary parameter scalar auxiliary)) := by
  rw [operationalIdealGame_eq]
  exact ThreePhase.concretePrivacy adversary parameter scalar auxiliary witness

end
end SimulatorMachine
end Kriterion.ArgoMAC.Security
