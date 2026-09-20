import Proof.Privacy.Simulator.Arithmetic.ProgramReindex
import Proof.Privacy.Simulator.Arithmetic.SharedSourceCutoff
import Proof.Privacy.Simulator.SharedOracleProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security
open Security.SimulatorMachine
noncomputable section

/-- The source compiler replaces each role index with its shared physical role. -/
def sharedInternalRequest : SimulatorMachine.spec.Query → SharedSimulatorMachine.spec.Query
  | .read (.fixedForward index input) => .read (.fixedForward (Shared.fixedIndex index) input)
  | .read (.fixedInverse index output) => .read (.fixedInverse (Shared.fixedIndex index) output)
  | .read (.encForward index input) => .read (.encForward index input)
  | .read (.encInverse index output) => .read (.encInverse index output)
  | .read (.hash input) => .read (.hash input)
  | .program command => .program (Shared.fixedIndex command.1, command.2)

/-- The shared source compiler preserves each typed answer. -/
def sharedInternalAnswer : (request : SimulatorMachine.spec.Query) →
    SharedSimulatorMachine.spec.Answer (sharedInternalRequest request) → SimulatorMachine.spec.Answer request
  | .read (.fixedForward _ _), value => value
  | .read (.fixedInverse _ _), value => value
  | .read (.encForward _ _), value => value
  | .read (.encInverse _ _), value => value
  | .read (.hash _), value => value
  | .program _, value => value

/-- The reindexed eager handler implements the existing three-slot command interpreter. -/
theorem sharedInternalRequest_handler (request : SimulatorMachine.spec.Query)
    (state : SharedSimulatorMachine.SharedState) :
    (let result := SharedSimulatorMachine.handler (sharedInternalRequest request) state
     (sharedInternalAnswer request result.1, result.2)) = Shared.Simulator.Source.handler request state := by
  cases request with
  | read query => cases query <;> rfl
  | program command => rfl

/-- The source program preserves its complete run under shared query conversion. -/
theorem sharedInternalProgram_run {A : Type} {budget : Nat}
    (program : Program SimulatorMachine.spec A budget) (state : SharedSimulatorMachine.SharedState) :
    (program.reindex sharedInternalRequest sharedInternalAnswer).run SharedSimulatorMachine.handler state =
      program.run Shared.Simulator.Source.handler state := by
  rw [Program.reindex_run]
  have handlers : (fun request state =>
      let result := SharedSimulatorMachine.handler (sharedInternalRequest request) state
      (sharedInternalAnswer request result.1, result.2)) = Shared.Simulator.Source.handler := by
    funext request state
    exact sharedInternalRequest_handler request state
  rw [handlers]

/-- The combined program marks each reindexed command as an internal operation. -/
def sharedCombinedProgram {A : Type} {budget : Nat} (program : Program SimulatorMachine.spec A budget) :
    Program SharedSimulatorMachine.combinedSpec A budget :=
  (program.reindex sharedInternalRequest sharedInternalAnswer).reindex Sum.inl (fun _ value => value)

/-- The combined source program has the exact three-slot eager run. -/
theorem sharedCombinedProgram_run {A : Type} {budget : Nat}
    (program : Program SimulatorMachine.spec A budget) (state : SharedSimulatorMachine.SharedState) :
    (sharedCombinedProgram program).run SharedSimulatorMachine.combinedEager state =
      program.run Shared.Simulator.Source.handler state := by
  rw [sharedCombinedProgram, Program.reindex_run]
  exact sharedInternalProgram_run program state

/-- The source compiler preserves the exact valid online schedule and labels. -/
theorem sharedCombined_valid_run [FieldCertificate] [GroupCertificate]
    (state : Shared.Simulator.State) (input : AffineInput) (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    (sharedCombinedProgram (validProgram state input output free scales)).run SharedSimulatorMachine.combinedEager state.oracle =
      (state.labels input, Shared.Simulator.program state.oracle (state.selectedSchedule input output free scales)) := by
  rw [sharedCombinedProgram_run]
  exact Shared.Simulator.Source.valid_run state input output free scales

/-- The source compiler preserves the exact invalid online schedule and labels. -/
theorem sharedCombined_invalid_run (state : Shared.Simulator.State) (input : AffineInput) :
    (sharedCombinedProgram (invalidProgram state input)).run SharedSimulatorMachine.combinedEager state.oracle =
      (state.labels input, Shared.Simulator.program state.oracle
        ((state.selectedCurve input).schedule input (state.labels input).inputMac)) := by
  rw [sharedCombinedProgram_run]
  exact Shared.Simulator.Source.invalid_run state input

end
end Kriterion.ArgoMAC.ArithmeticSimulator
