import Proof.Privacy.Simulator.Arithmetic.GateDriverJointSource
import Proof.Privacy.Simulator.Arithmetic.SharedSourceProgram
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

/-- The shared compiler changes only the fixed permutation index of each command. -/
def sharedCommand (command : FixedCommand) : SharedCommand :=
  (Shared.fixedIndex command.1, command.2)

/-- The compiled command list has the exact coupled gate source law. -/
theorem sharedCombinedCommands_cutoff [BN254.FieldCertificate] (attempts : Nat) (values : List FixedCommand)
    (state : SharedOracleSource) :
    (sharedCombinedProgram (SimulatorMachine.commands values)).cutoffLaw (sharedSourceCutoff attempts) state =
      sharedCommandListCutoff attempts (values.map sharedCommand) state := by
  induction values generalizing state with
  | nil => rfl
  | cons command rest ih =>
    change bindCutoff (sharedSourceCutoff attempts (.inl (.program (sharedCommand command))) state)
      (fun result => (sharedCombinedProgram (SimulatorMachine.commands rest)).cutoffLaw
        (sharedSourceCutoff attempts) result.2) = _
    simp only [ih, List.map_cons, sharedCommandListCutoff]

/-- The complete OracleProgram uses the same coupled command source law. -/
theorem sharedCombinedCommands_toOracle [BN254.FieldCertificate] (attempts : Nat) (values : List FixedCommand)
    (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) (sharedCombinedProgram (SimulatorMachine.commands values)).toOracle state =
      sharedCommandListCutoff attempts (values.map sharedCommand) state := by
  rw [Program.cutoffLaw_toOracle]
  exact sharedCombinedCommands_cutoff attempts values state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
