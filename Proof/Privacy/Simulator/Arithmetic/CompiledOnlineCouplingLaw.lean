import Proof.Privacy.Simulator.Arithmetic.CompiledDecisionProtocol
import Proof.Privacy.Simulator.Arithmetic.SharedParsedGame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- The online joint retains typed labels and both complete states. -/
abbrev SharedOnlineJoint [FieldCertificate] := SimulatorSampling.OfflineCoin → AffineInput → Option Point → State → SharedOracleSource →
  PMF (Option (Garbling.Labels × (State × SharedOracleSource)))

/-- The online interface states the exact two marginals and the final decision reserve. -/
def CompiledOnlineCouplingLaw [FieldCertificate] [GroupCertificate] (online : SharedOnlineJoint) : Prop :=
  ∀ (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Option Point)
    (used setupSpent : Nat) (state : State) (source : SharedOracleSource),
    used < 2 ^ 101 → setupSpent ≤ 2 ^ 30 + 605084290688 + 2 →
    CompiledPublicReady 256 0 0 0 setupSpent used state source →
    WordsAt state.memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin) →
    ((online coin input output state source).map
      (Option.map fun result => (Lamport.selectedLabels result.1.inputMac, result.2.1)) =
      sharedParsedOnline (compiledMachine 256) state input output) ∧
    ((online coin input output state source).map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff 256) (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input output) source) ∧
    ∀ labels final, some (labels, final) ∈ (online coin input output state source).support →
      CompiledDecisionReady used final.1 final.2

end
end Kriterion.ArgoMAC.ArithmeticSimulator
