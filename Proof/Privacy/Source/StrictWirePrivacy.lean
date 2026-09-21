import Proof.Privacy.Source.StrictSourceSampling
import Proof.Privacy.Simulator.SharedChallengePrivacy
import Proof.SharedOracle

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions GarbledCircuit
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The wire source has the same strict privacy error. The source layer samples the
internal table, so its adversary reads `Pipeline.Table`; the transmitted wire game
hands its adversary the packed table, which is exactly what `rebase` restores. -/
theorem sharedStrictWireAdvantage_envelope [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101) :
    advantage
      (realGame Shared.packedCircuit (uniformRandomTape Shared.Randomness witness)
        sharedRealOracleHandler adversary parameter scalar auxiliary)
      (sharedStrictSourceDecision SimulatorSampling.offline.law SimulatorSampling.online.law
        ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
        parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  rw [sharedStrictSourceDecision_exact]
  have bound := sharedStrictAdaptiveAdvantage_envelope
    ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
    parameter auxiliary scalar witness small
  simpa only [realGame, sharedWireAdversary, AdaptiveAdversary.rebase, Shared.packedCircuit,
    Shared.wireCircuit, sharedInternalCircuit, GarbledCircuit.mapPublic, Lamport.wireCircuit,
    GarbledCircuit.mapLabels, PMF.bind_map, Function.comp_def, Garbling.topology] using bound

/-- The finite private samplers preserve the required work bound. -/
theorem sharedStrictWirePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness) :
    WorkPerAdvantage 100 (adversaryWork adversary parameter)
      (advantage
        (realGame Shared.packedCircuit (uniformRandomTape Shared.Randomness witness)
          sharedRealOracleHandler adversary parameter scalar auxiliary)
        (sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
          (SimulatorSampling.online.total 256).law
          ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
          parameter scalar auxiliary)) := by
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  apply adaptivePrivacyTransfer (ideal := sharedStrictSourceDecision SimulatorSampling.offline.law
    SimulatorSampling.online.law ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
    parameter scalar auxiliary)
  by_cases small : queries < 2 ^ 101
  · apply sharedErrors_has100Bits queries
    · exact sharedStrictWireAdvantage_envelope adversary parameter auxiliary scalar witness (Nat.le_of_lt small)
    · exact sharedStrictSourceDecision_allowance
        ((sharedWireAdversary adversary).rebase Pipeline.Table.pack) parameter scalar auxiliary
  · exact sharedLargeBudget_has100Bits _ _ _ queries (Nat.le_of_not_gt small)

/-- A closed implementation of the finite source meets the public privacy rule. -/
theorem sharedStrictOraclePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Shared.PrivateCoins] (witness : Shared.Randomness)
    (simulator : BoundedMachine.Simulator)
    (implementation : ∀ (adversary : AdaptiveAdversary sharedRealOracleSpec
        AffineInput Pipeline.PackedTable LamportSignature Unit) parameter scalar,
      LazySimulatorProtocol.idealGame Shared.packedProgramCircuit Wire.encoding 8887896 simulator
        adversary parameter scalar () =
      sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
        (SimulatorSampling.online.total 256).law
        ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
        parameter scalar ()) :
    OracleAdaptivePrivacy Shared.packedProgramCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.PrivateCoins (Shared.privateCoins witness))
      (fun parameter scalar random => (Shared.packedGarbleProgram parameter scalar random).toOracleProgram) := by
  refine ⟨simulator, fun machine parameter scalar => ?_⟩
  dsimp only
  rw [OperationalOracle.packed_shared_lazy_real, implementation]
  apply le_trans (sharedStrictWirePrivacy (machineAdversary Wire.encoding machine)
    parameter () scalar witness)
  apply Nat.cast_le.mpr
  simp only [adversaryWork, machineAdversary, BoundedMachine.Adversary.steps]
  omega

end
end Kriterion.ArgoMAC.Security
