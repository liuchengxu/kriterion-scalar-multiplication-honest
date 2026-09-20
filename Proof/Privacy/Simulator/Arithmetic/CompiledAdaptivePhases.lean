import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineCouplingLaw
import Proof.Privacy.Simulator.Arithmetic.CutoffMapBind

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples runProgram offlineSchedule

theorem cutoff_bind_project {A B C : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (input : A → C) (target : C → PMF (Option B))
    (law : ∀ value, some value ∈ source.support → next value = target (input value)) :
    bindCutoff source next = bindCutoff (source.map (Option.map input)) target := by
  have projected := cutoff_map_bind source next input id target (by
    intro value member
    simpa only [Option.map_id, PMF.map_id] using law value member)
  simpa only [Option.map_id, PMF.map_id] using projected

/-- The decision joint observes the final Boolean and discards both private states. -/
def compiledDecisionJoint [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (pair : State × SharedOracleSource) : PMF (Option Bool) :=
  (runSampledCutoff (fun request pair => compiledQueryCoupledSamples 256 pair.1 pair.2 request)
    (sharedWireSourceDecide adversary parameter auxiliary coin selected labels) pair).map (Option.map Prod.fst)

/-- The complete decision has both exact final Boolean marginals. -/
theorem compiledDecisionJoint_law [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (pair : State × SharedOracleSource)
    (used : Nat) (ready : CompiledDecisionReady used pair.1 pair.2)
    (small : used + adversary.secondQueryBudget parameter < 2 ^ 101) :
    compiledDecisionJoint adversary parameter auxiliary coin selected labels pair =
      ((runProgram (compiledMachine 256)
        (sharedWireSourceDecide adversary parameter auxiliary coin selected labels) pair.1).run).map (Option.map Prod.fst) ∧
    compiledDecisionJoint adversary parameter auxiliary coin selected labels pair =
      (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
        (sharedWireSourceDecide adversary parameter auxiliary coin selected labels) pair.2).map (Option.map Prod.fst) := by
  have laws := compiledDecisionProtocol used pair.1 pair.2 ready
    (sharedWireSourceDecide adversary parameter auxiliary coin selected labels) small
  constructor
  · have law := congrArg (PMF.map (Option.map Prod.fst)) laws.1
    simpa only [compiledDecisionJoint, PMF.map_comp, Option.map_map, Function.comp_def] using law
  · have law := congrArg (PMF.map (Option.map Prod.fst)) laws.2.1
    simpa only [compiledDecisionJoint, PMF.map_comp, Option.map_map, Function.comp_def] using law

/-- The online joint passes its exact labels and states to the final decision. -/
def compiledOnlineDecision [FieldCertificate] {Aux : Type} (online : SharedOnlineJoint)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin)
    (selected : AffineInput × adversary.State) (output : Option Point) (pair : State × SharedOracleSource) : PMF (Option Bool) :=
  bindCutoff (online coin selected.1 output pair.1 pair.2) fun encoded =>
    compiledDecisionJoint adversary parameter auxiliary coin selected encoded.1 encoded.2

/-- The online and decision phases preserve both complete experiment marginals. -/
theorem compiledOnlineDecision_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : SharedOnlineJoint) (implemented : CompiledOnlineCouplingLaw online)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : SimulatorSampling.OfflineCoin)
    (selected : AffineInput × adversary.State) (output : Option Point) (pair : State × SharedOracleSource)
    (used setupSpent : Nat) (small : used + adversary.secondQueryBudget parameter < 2 ^ 101)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (ready : CompiledPublicReady 256 0 0 0 setupSpent used pair.1 pair.2)
    (stored : WordsAt pair.1.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    compiledOnlineDecision online adversary parameter auxiliary coin selected output pair =
      (bindCutoff (sharedParsedOnline (compiledMachine 256) pair.1 selected.1 output) fun encoded =>
        ((runProgram (compiledMachine 256)
          (adversary.decide parameter (publicSourceTable coin.1) encoded.1 auxiliary selected.2) encoded.2).run).map (Option.map Prod.fst)) ∧
    compiledOnlineDecision online adversary parameter auxiliary coin selected output pair =
      bindCutoff (runSampledCutoff (sharedSourceCutoff 256)
        (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) selected.1 output) pair.2) fun encoded =>
          (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
            (sharedWireSourceDecide adversary parameter auxiliary coin selected encoded.1) encoded.2).map (Option.map Prod.fst) := by
  have onlineLaw := implemented coin selected.1 output used setupSpent pair.1 pair.2 (by omega) setup ready stored
  constructor
  · unfold compiledOnlineDecision
    rw [← onlineLaw.1]
    apply cutoff_bind_project
    intro encoded member
    exact (compiledDecisionJoint_law adversary parameter auxiliary coin selected encoded.1 encoded.2 used
      (onlineLaw.2.2 encoded.1 encoded.2 member) small).1
  · unfold compiledOnlineDecision
    rw [← onlineLaw.2.1]
    apply cutoff_bind_project
    intro encoded member
    exact (compiledDecisionJoint_law adversary parameter auxiliary coin selected encoded.1 encoded.2 used
      (onlineLaw.2.2 encoded.1 encoded.2 member) small).2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
