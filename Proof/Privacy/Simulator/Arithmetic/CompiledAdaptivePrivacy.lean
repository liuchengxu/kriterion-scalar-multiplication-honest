import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptiveGame
import Proof.Privacy.Simulator.Arithmetic.OnlineJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SharedSimulatorMachine
noncomputable section

/-- The checked complete game closes privacy when the concrete online joint satisfies its exact law. -/
theorem compiledAdaptivePrivacy_of_onlineLaw [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Shared.Randomness)
    (implemented : CompiledOnlineCouplingLaw (compiledOnlineJoint 256)) :
    GarbledCircuit.AdaptivePrivacy (Aux := Aux) Shared.packedCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler
      circuitSimulatorOracleHandler CircuitSimulatorState.view := by
  apply sharedAdaptivePrivacy_of_finiteSource witness (compiledMachine 256)
  intro adversary parameter scalar auxiliary small
  exact compiledIdealGame_finiteSource (compiledOnlineJoint 256) implemented adversary parameter scalar auxiliary small

end
end Kriterion.ArgoMAC.ArithmeticSimulator
