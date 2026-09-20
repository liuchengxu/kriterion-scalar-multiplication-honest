import Proof.Privacy.Simulator.Arithmetic.CompiledValidProtocol
import Proof.Privacy.Simulator.Arithmetic.CompiledNullProtocol
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptivePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SharedSimulatorMachine
noncomputable section

/-- Both concrete online branches satisfy the complete source and machine coupling. -/
theorem compiledOnlineJoint_coupling [FieldCertificate] [GroupCertificate] :
    CompiledOnlineCouplingLaw (compiledOnlineJoint 256) := by
  intro coin input output used setupSpent state source small setup initial stored
  cases output with
  | none => exact compiledNullJoint_coupling coin input used setupSpent state source small setup initial stored
  | some output => exact compiledValidJoint_coupling coin input output used setupSpent state source small setup initial stored

/-- The concrete fixed instruction machine satisfies the complete revised adaptive privacy property. -/
theorem compiledAdaptivePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Shared.Randomness) :
    GarbledCircuit.AdaptivePrivacy (Aux := Aux) Shared.packedCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler
      circuitSimulatorOracleHandler CircuitSimulatorState.view :=
  compiledAdaptivePrivacy_of_onlineLaw witness compiledOnlineJoint_coupling

end
end Kriterion.ArgoMAC.ArithmeticSimulator
