import Proof.Privacy.Simulator.Arithmetic.SharedExactSourceGame
import Proof.Privacy.Simulator.SharedChallengePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.Assumptions Security Security.SharedSimulatorMachine GarbledCircuit
noncomputable section

/-- The finite source uses the exact challenge table, labels, and adaptive adversary. -/
def sharedWireFiniteDecision [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  sharedFiniteSourceDecision 256 sharedOfflineFrame (sharedWireSourceChoose adversary parameter auxiliary)
    Prod.fst (fun selected => Shared.wireCircuit.function scalar selected.1)
    (sharedWireSourceDecide adversary parameter auxiliary) (fun _ => initialSharedOracleSource emptySharedMetadata)

/-- The complete finite source meets the final concrete machine-error allowance. -/
theorem sharedWireFiniteDecision_bound [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    advantage
      (idealGame Shared.packedCircuit (fun _ => 8887896) Shared.Simulator.packedWireSimulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary)
      (sharedWireFiniteDecision adversary parameter scalar auxiliary) ≤
      sharedMachineCutoffAllowance (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  have bound := sharedFiniteSourceDecision_allowance sharedOfflineFrame (sharedWireSourceChoose adversary parameter auxiliary)
    Prod.fst (fun selected => Shared.wireCircuit.function scalar selected.1)
    (sharedWireSourceDecide adversary parameter auxiliary) (fun _ => initialSharedOracleSource emptySharedMetadata)
  rw [sharedExactSourceDecision_idealGame] at bound
  change advantage _ _ ≤ _ at bound
  unfold advantage at bound ⊢
  rw [abs_sub_comm]
  simpa only [sharedWireFiniteDecision, sharedMachineCutoffAllowance, Nat.cast_add, Nat.cast_ofNat] using bound

/-- An exact machine-to-source game law closes the revised challenge property. -/
theorem sharedAdaptivePrivacy_of_finiteSource [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (witness : Shared.Randomness) (machine : BoundedMachine.Machine)
    (implementation : ∀ (adversary : AdaptiveAdversary sharedRealOracleSpec
        AffineInput Pipeline.PackedTable LamportSignature Aux) parameter scalar auxiliary,
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 101 →
      SimulatorProtocol.idealGame Shared.packedCircuit Wire.encoding 8887896 machine adversary parameter scalar auxiliary =
        sharedWireFiniteDecision adversary parameter scalar auxiliary) :
    AdaptivePrivacy (Aux := Aux) Shared.packedCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler
      circuitSimulatorOracleHandler CircuitSimulatorState.view := by
  apply sharedAdaptivePrivacy_of_machine witness machine
  intro adversary parameter scalar auxiliary queries small
  rw [implementation adversary parameter scalar auxiliary small]
  exact sharedWireFiniteDecision_bound adversary parameter scalar auxiliary

end
end Kriterion.ArgoMAC.ArithmeticSimulator
