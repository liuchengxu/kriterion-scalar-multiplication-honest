import Proof.Privacy.Simulator.SimulatorExecution

namespace Kriterion.ArgoMAC.Security.SimulatorCommandCost
open BN254 Cryptography

/-- The charge covers the location test, tweak conversion, window reduction,
index and tuple construction, record reads, and two XOR operations.
The index operations use the schedule's bounded coordinate indices. -/
def commandWithCost (location : Pipeline.FixedKeyLocation) (window : Nat)
    (label : Block) (slot : Pipeline.FixedKeySlot) (block : Block) : FixedCommand × Nat :=
  ((fixedKeyIndex location window slot, gateInput location label, block ^^^ label), 20)

/-- The compiler constructs the selected commands in execution order.
The pad branch charges the field encoding, ciphertext XOR, two block extractions,
and local reads and list writes. The hash branch charges three block extractions,
and local reads and list writes. -/
def gateCommandsWithCost (directive : GateDirective) : List FixedCommand × Nat :=
  if directive.bit then
    let bytes := directive.table.trueRow ^^^ BitAdaptor.fieldBytes directive.target
    let first := commandWithCost directive.location directive.window directive.label
      (.pad 0) (bytes.extractLsb' 0 128)
    let second := commandWithCost directive.location directive.window directive.label
      (.pad 1) (bytes.extractLsb' 128 128)
    ([first.1, second.1], first.2 + second.2 + 16)
  else
    let bytes := directive.lift.1
    let first := commandWithCost directive.location directive.window directive.label
      (.hash 0) (bytes.extractLsb' 0 128)
    let second := commandWithCost directive.location directive.window directive.label
      (.hash 1) (bytes.extractLsb' 128 128)
    let third := commandWithCost directive.location directive.window directive.label
      (.hash 2) (bytes.extractLsb' 256 128)
    ([first.1, second.1, third.1], first.2 + second.2 + third.2 + 16)

theorem gateCommandsWithCost_value (directive : GateDirective) :
    (gateCommandsWithCost directive).1 = directive.commands := by
  cases directive with
  | mk location window bit label table target lift =>
    cases bit <;> rfl

theorem gateCommandsWithCost_bound (directive : GateDirective) :
    (gateCommandsWithCost directive).2 ≤ 76 := by
  unfold gateCommandsWithCost
  split <;> simp only [commandWithCost] <;> decide

/-- The append counter charges one list read and one list write per copied command. -/
def appendWithCost (tail : List FixedCommand) : List FixedCommand → List FixedCommand × Nat
  | [] => (tail, 0)
  | command :: rest =>
    let result := appendWithCost tail rest
    (command :: result.1, result.2 + 2)

theorem appendWithCost_value (tail values : List FixedCommand) :
    (appendWithCost tail values).1 = values ++ tail := by
  induction values with
  | nil => rfl
  | cons command rest ih => simp only [appendWithCost, ih, List.cons_append]

theorem appendWithCost_cost (tail values : List FixedCommand) :
    (appendWithCost tail values).2 = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons command rest ih => simp only [appendWithCost, ih, List.length_cons]; omega

/-- The compiler charges command construction and every copied command.
Each schedule entry also costs one list read and one branch operation. -/
def scheduleCommandsWithCost : List GateDirective → List FixedCommand × Nat
  | [] => ([], 0)
  | directive :: rest =>
    let head := gateCommandsWithCost directive
    let tail := scheduleCommandsWithCost rest
    let joined := appendWithCost tail.1 head.1
    (joined.1, head.2 + tail.2 + joined.2 + 2)

theorem scheduleCommandsWithCost_value (schedule : List GateDirective) :
    (scheduleCommandsWithCost schedule).1 = scheduleCommands schedule := by
  induction schedule with
  | nil => rfl
  | cons directive rest ih =>
    simp only [scheduleCommandsWithCost, appendWithCost_value, gateCommandsWithCost_value,
      ih, scheduleCommands, List.flatMap_cons]

theorem scheduleCommandsWithCost_bound (schedule : List GateDirective) :
    (scheduleCommandsWithCost schedule).2 ≤ 100 * schedule.length := by
  induction schedule with
  | nil => simp [scheduleCommandsWithCost]
  | cons directive rest ih =>
    have head := gateCommandsWithCost_bound directive
    have length := directive.commands_length
    simp only [scheduleCommandsWithCost, appendWithCost_cost, gateCommandsWithCost_value,
      List.length_cons]
    omega

/-- The complete valid schedule has this command-construction budget. -/
theorem scheduleCommandsWithCost_valid_bound (schedule : List GateDirective)
    (bounded : schedule.length ≤ 278638) :
    (scheduleCommandsWithCost schedule).2 ≤ 27863800 := by
  exact (scheduleCommandsWithCost_bound schedule).trans (Nat.mul_le_mul_left 100 bounded)

end Kriterion.ArgoMAC.Security.SimulatorCommandCost
