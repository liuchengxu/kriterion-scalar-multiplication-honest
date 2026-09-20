import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptivePhases

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples runProgram offlineSchedule

/-- The full adaptive continuation keeps the sampled setup coin and both oracle states. -/
def compiledChosenDecision [FieldCertificate] [GroupCertificate] {Aux : Type} (online : SharedOnlineJoint)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (state : State) (coin : SimulatorSampling.OfflineCoin) : PMF (Option Bool) :=
  bindCutoff (runSampledCutoff (fun request pair => compiledQueryCoupledSamples 256 pair.1 pair.2 request)
    (sharedWireSourceChoose adversary parameter auxiliary coin) (state, initialSharedOracleSource emptySharedMetadata)) fun selected =>
      compiledOnlineDecision online adversary parameter auxiliary coin selected.1
        (Shared.wireCircuit.function scalar selected.1.1) selected.2

/-- The chosen-input continuation has the exact actual and finite-source experiment laws. -/
theorem compiledChosenDecision_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : SharedOnlineJoint) (implemented : CompiledOnlineCouplingLaw online)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (state : State) (coin : SimulatorSampling.OfflineCoin)
    (setup : (state, coin) ∈ (compiledSetupJoint 256 parameter).support)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 101) :
    compiledChosenDecision online adversary parameter scalar auxiliary state coin =
      (bindCutoff (runProgram (compiledMachine 256) (sharedWireSourceChoose adversary parameter auxiliary coin) state).run fun selected =>
        bindCutoff (sharedParsedOnline (compiledMachine 256) selected.2 selected.1.1
          (Shared.wireCircuit.function scalar selected.1.1)) fun encoded =>
            ((runProgram (compiledMachine 256)
              (adversary.decide parameter (publicSourceTable coin.1) encoded.1 auxiliary selected.1.2) encoded.2).run).map
                (Option.map Prod.fst)) ∧
    compiledChosenDecision online adversary parameter scalar auxiliary state coin =
      bindCutoff (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
        (sharedWireSourceChoose adversary parameter auxiliary coin) (initialSharedOracleSource emptySharedMetadata)) fun selected =>
          bindCutoff (runSampledCutoff (sharedSourceCutoff 256)
            (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) selected.1.1 (Shared.wireCircuit.function scalar selected.1.1)) selected.2) fun encoded =>
              (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
                (sharedWireSourceDecide adversary parameter auxiliary coin selected.1 encoded.1) encoded.2).map (Option.map Prod.fst) := by
  have chosen := compiledChosenProtocol parameter state coin setup
    (sharedWireSourceChoose adversary parameter auxiliary coin) (by omega)
  have cost := compiledSetupJoint_fixedCost parameter state coin setup
  constructor
  · unfold compiledChosenDecision
    rw [← chosen.1]
    apply cutoff_bind_project
    intro selected member
    obtain ⟨used, bound, ready, stored⟩ := chosen.2.2 selected.1 selected.2 member
    exact (compiledOnlineDecision_law online implemented adversary parameter auxiliary coin selected.1
      (Shared.wireCircuit.function scalar selected.1.1) selected.2 used state.spent (by omega) cost ready stored).1
  · unfold compiledChosenDecision
    rw [← chosen.2.1]
    apply cutoff_bind_project
    intro selected member
    obtain ⟨used, bound, ready, stored⟩ := chosen.2.2 selected.1 selected.2 member
    exact (compiledOnlineDecision_law online implemented adversary parameter auxiliary coin selected.1
      (Shared.wireCircuit.function scalar selected.1.1) selected.2 used state.spent (by omega) cost ready stored).2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
