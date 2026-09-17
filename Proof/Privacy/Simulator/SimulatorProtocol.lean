import Proof.Privacy.Simulator.OperationalSimulator
import Proof.Privacy.Simulator.SimulatorOracleProgram

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
namespace SimulatorMachine
open SimulatorSampling

/-- The private coin and the current oracle state determine the semantic simulator state. -/
def privateState (coin : OfflineCoin) (oracle : SimulatorState) : CircuitSimulatorState where
  oracle := oracle
  curve := coin.1.curveRequest
  points := coin.1.pointRequests
  inputKey := coin.2.1
  bridgeKey := coin.2.2

/-- The program uses this constant environment only to construct its private arguments. -/
def privateView (coin : OfflineCoin) : CircuitSimulatorState :=
  privateState coin {
    fixedOracle := ⟨fun _ => Equiv.refl _⟩
    encOracle := ⟨fun _ => Equiv.refl _⟩
    hashOracle := fun _ => (0, 0)
    fixedTranscript := [], encTranscript := [], hashTranscript := []
    commitments := [], linking := none, bad := false }

/-- Changing the oracle environment does not change the valid program. -/
theorem validProgram_private [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (oracle : SimulatorState) (input : AffineInput)
    (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    validProgram (privateView coin) input output free scales =
      validProgram (privateState coin oracle) input output free scales := rfl

/-- Changing the oracle environment does not change the invalid program. -/
theorem invalidProgram_private (coin : OfflineCoin) (oracle : SimulatorState)
    (input : AffineInput) :
    invalidProgram (privateView coin) input = invalidProgram (privateState coin oracle) input := rfl

/-- The valid private program updates the exact semantic oracle state. -/
theorem validProgram_private_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (oracle : SimulatorState) (input : AffineInput)
    (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    (validProgram (privateView coin) input output free scales).run handler oracle =
      ((privateView coin).labels input,
        ((privateState coin oracle).programForOutput input output free scales).oracle) := by
  rw [validProgram_private coin oracle]
  exact validProgram_run (privateState coin oracle) input output free scales

/-- The invalid private program updates the exact semantic oracle state. -/
theorem invalidProgram_private_run (coin : OfflineCoin) (oracle : SimulatorState)
    (input : AffineInput) :
    (invalidProgram (privateView coin) input).run handler oracle =
      ((privateView coin).labels input, programGateSchedule oracle
        ((privateView coin).selectedCurve input |>.schedule input ((privateView coin).labels input).inputMac)) := by
  rw [invalidProgram_private coin oracle]
  exact invalidProgram_run (privateState coin oracle) input

/-- The online operation budget includes internal reads and all programming attempts. -/
abbrev onlineBudget [FieldCertificate] (output : Option Point) : Nat := if output.isSome then 836423 else 3810

/-- This oracle program samples private online coins before it executes the selected path. -/
noncomputable def encodeProgram [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (input : AffineInput) (output : Option Point) :
    OracleProgram spec Garbling.Labels (onlineBudget output) :=
  match output with
  | none => (invalidProgram (privateView coin) input).toOracle
  | some point => ThreePhase.append
      (fun sample => (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2).toOracle)
      (.pure online.law)

/-- The operational online program has the original joint label and oracle distribution. -/
theorem encodeProgram_law [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (oracle : SimulatorState) (input : AffineInput) (output : Option Point) :
    (encodeProgram coin input output).run handler oracle =
      (concreteCircuitSimulator.simulateEncode (privateState coin oracle) input output).map
        (fun answer => (answer.1, answer.2.oracle)) := by
  cases output with
  | none =>
      simp only [encodeProgram, Program.toOracle_run, invalidProgram_private_run,
        concreteCircuitSimulator, circuitSimulator, PMF.pure_map]
      rfl
  | some point =>
      simp only [encodeProgram, ThreePhase.run_append, OracleProgram.run_pure, PMF.bind_map,
        Program.toOracle_run, validProgram_private_run,
        concreteCircuitSimulator, circuitSimulator, PMF.map_comp, Function.comp_def]
      rw [online_uniform]
      rfl

/-- Each valid execution makes at most 836423 oracle calls. -/
theorem validProgram_call_bound [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (oracle : SimulatorState) (input : AffineInput)
    (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    ((validProgram (privateView coin) input output free scales).runCount handler oracle).2 ≤ 836423 :=
  (Program.runCount_correct handler _ oracle).2

/-- Each invalid execution makes at most 3810 oracle calls. -/
theorem invalidProgram_call_bound (coin : OfflineCoin) (oracle : SimulatorState)
    (input : AffineInput) :
    ((invalidProgram (privateView coin) input).runCount handler oracle).2 ≤ 3810 :=
  (Program.runCount_correct handler _ oracle).2

end SimulatorMachine
end Kriterion.ArgoMAC.Security
