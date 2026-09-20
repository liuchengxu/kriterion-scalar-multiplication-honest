import Proof.Privacy.SharedConcreteAdaptivePrivacy
import Proof.Privacy.Bounds.SharedMachineArithmetic
import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions GarbledCircuit
noncomputable section

/-- The adapter gives the wire adversary the exact selected Lamport blocks. -/
def sharedWireAdversary {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux) :
    AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable Garbling.Labels Aux := {
  State := adversary.State
  firstQueryBudget := adversary.firstQueryBudget
  secondQueryBudget := adversary.secondQueryBudget
  chooseInput := adversary.chooseInput
  decide := fun parameter table labels => adversary.decide parameter table (Lamport.selectedLabels labels.inputMac)
}

/-- The wire game retains the complete shared adaptive advantage bound. -/
theorem sharedWireAdvantage_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    advantage
      (realGame Shared.packedCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary)
      (idealGame Shared.packedCircuit (fun _ => 8887896) Shared.Simulator.packedWireSimulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  have bound := sharedAdaptiveAdvantage_envelope
    ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
    parameter auxiliary scalar witness small
  simpa only [realGame, idealGame, sharedWireAdversary, AdaptiveAdversary.rebase, Shared.packedCircuit,
    Shared.wireCircuit, sharedInternalCircuit, GarbledCircuit.mapPublic, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, Shared.Simulator.packedWireSimulator, Shared.Simulator.wireSimulator,
    Simulator.mapPublic, Simulator.mapLabels, PMF.bind_map, Function.comp_def, Garbling.topology] using bound

/-- A concrete machine error bound closes the single adaptive privacy property. -/
theorem sharedAdaptivePrivacy_of_machine [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Shared.Randomness) (machine : BoundedMachine.Machine)
    (implementation : ∀ (adversary : AdaptiveAdversary sharedRealOracleSpec
        AffineInput Pipeline.PackedTable LamportSignature Aux) parameter scalar auxiliary,
      let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
      queries < 2 ^ 101 →
      advantage
        (idealGame Shared.packedCircuit (fun _ => 8887896) Shared.Simulator.packedWireSimulator
          circuitSimulatorOracleHandler adversary parameter scalar auxiliary)
        (SimulatorProtocol.idealGame Shared.packedCircuit Wire.encoding 8887896 machine
          adversary parameter scalar auxiliary) ≤ sharedMachineCutoffAllowance queries) :
    AdaptivePrivacy (Aux := Aux) Shared.packedCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler
      circuitSimulatorOracleHandler CircuitSimulatorState.view := by
  refine ⟨Shared.Simulator.packedWireSimulator, machine,
    Shared.Simulator.wire_oracleSimulation.mapPublic Pipeline.Table.pack, ?_⟩
  intro adversary parameter scalar auxiliary
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  by_cases small : queries < 2 ^ 101
  · apply sharedErrors_has100Bits queries
    · exact sharedWireAdvantage_envelope adversary parameter auxiliary scalar witness (Nat.le_of_lt small)
    · exact implementation adversary parameter scalar auxiliary small
  · exact sharedLargeBudget_has100Bits _ _ _ queries (Nat.le_of_not_gt small)

end
end Kriterion.ArgoMAC.Security
