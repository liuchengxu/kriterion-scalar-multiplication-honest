import Proof.Privacy.Simulator.ConcreteSimulator

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography

/-- Each command programs one selected permutation pair. -/
abbrev FixedCommand := Pipeline.FixedKeyIndex × Block × Block

/-- The command order agrees with the gate evaluator. -/
def GateDirective.commands (directive : GateDirective) : List FixedCommand :=
  directive.programRecords.reverse.map fun record => (record.index, record.domain, record.range)

/-- The interpreter keeps the original collision behavior. -/
def executeFixed (state : SimulatorState) (command : FixedCommand) : SimulatorState :=
  tryProgramFixed state command.1 command.2.1 command.2.2

/-- The interpreter executes a finite command list. -/
def executeFixedCommands (state : SimulatorState) (commands : List FixedCommand) : SimulatorState :=
  commands.foldl executeFixed state

theorem GateDirective.commands_correct (directive : GateDirective) (state : SimulatorState) :
    executeFixedCommands state directive.commands = directive.apply state := by
  cases directive with
  | mk location window bit label table target lift =>
    cases bit <;>
      rfl

/-- One gate makes at most three programming attempts. -/
theorem GateDirective.commands_length (directive : GateDirective) :
    directive.commands.length ≤ 3 := by
  simp only [GateDirective.commands, List.length_map, List.length_reverse,
    GateDirective.programRecords]
  split <;> simp

/-- The compiler concatenates the gate commands in their execution order. -/
def scheduleCommands (schedule : List GateDirective) : List FixedCommand :=
  schedule.flatMap GateDirective.commands

theorem scheduleCommands_correct (schedule : List GateDirective) (state : SimulatorState) :
    executeFixedCommands state (scheduleCommands schedule) = programGateSchedule state schedule := by
  induction schedule generalizing state with
  | nil => rfl
  | cons directive rest inductionHypothesis =>
    simp only [scheduleCommands, List.flatMap_cons, executeFixedCommands, List.foldl_append]
    change executeFixedCommands (executeFixedCommands state directive.commands)
      (scheduleCommands rest) = programGateSchedule state (directive :: rest)
    rw [directive.commands_correct, inductionHypothesis]
    rfl

theorem scheduleCommands_length (schedule : List GateDirective) :
    (scheduleCommands schedule).length ≤ 3 * schedule.length := by
  induction schedule with
  | nil => simp [scheduleCommands]
  | cons directive rest inductionHypothesis =>
    simp only [scheduleCommands, List.flatMap_cons, List.length_append, List.length_cons] at *
    have current := directive.commands_length
    omega

/-- The cost counts one record comparison for each visited history entry. -/
def checkFixedCost (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (command : FixedCommand) : Bool × Nat :=
  match history with
  | [] => (true, 0)
  | record :: rest =>
    if record.index ≠ command.1 ∨
        (record.domain ≠ command.2.1 ∧ record.range ≠ command.2.2) then
      let tail := checkFixedCost rest command
      (tail.1, tail.2 + 1)
    else (false, 1)

theorem checkFixedCost_correct (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (command : FixedCommand) :
    (checkFixedCost history command).1 =
      freshPermutationPairCheck history command.1 command.2.1 command.2.2 := by
  induction history with
  | nil => rfl
  | cons record rest inductionHypothesis =>
    simp only [checkFixedCost, freshPermutationPairCheck, List.all_cons]
    split <;> simp_all [freshPermutationPairCheck]

theorem checkFixedCost_le (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (command : FixedCommand) : (checkFixedCost history command).2 ≤ history.length := by
  induction history with
  | nil => simp [checkFixedCost]
  | cons record rest inductionHypothesis =>
    simp only [checkFixedCost]
    split <;> simp_all

/-- The complete valid schedule uses at most 835914 programming attempts. -/
theorem selectedSchedule_commands_length [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    (scheduleCommands (state.selectedSchedule input output free scales)).length ≤ 835914 := by
  have bound := scheduleCommands_length (state.selectedSchedule input output free scales)
  rw [CircuitSimulatorState.selectedSchedule, linkedPipelineGateSchedule_length] at bound
  exact bound

end Kriterion.ArgoMAC.Security
