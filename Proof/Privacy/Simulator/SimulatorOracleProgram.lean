import Proof.Privacy.Simulator.SimulatorExecution
import Proof.Privacy.ThreePhasePrivacy

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
namespace SimulatorMachine

/-- Internal reads leave the adversary transcript unchanged. -/
inductive Request where
  | read (query : Garbling.OracleQuery)
  | program (command : FixedCommand)

abbrev spec : OracleSpec where
  Query := Request
  Answer
    | .read query => Garbling.OracleAnswer query
    | .program _ => Unit

/-- This handler is the eager specification of the simulator's oracle operations. -/
def handler : OracleHandler spec SimulatorState
  | .read (.fixedForward index input), state => (state.fixedOracle.permutation index input, state)
  | .read (.fixedInverse index output), state => ((state.fixedOracle.permutation index).symm output, state)
  | .read (.encForward index input), state => (state.encOracle.permutation index input, state)
  | .read (.encInverse index output), state => ((state.encOracle.permutation index).symm output, state)
  | .read (.hash input), state => (state.hashOracle input, state)
  | .program command, state => ((), executeFixed state command)

/-- This executable program contains deterministic computation and bounded oracle operations. -/
inductive Program (oracle : OracleSpec.{0, 0}) : Type → Nat → Type 1
  | pure {A : Type} (value : A) : Program oracle A 0
  | query {A : Type} {budget : Nat} (request : oracle.Query)
      (next : oracle.Answer request → Program oracle A budget) : Program oracle A (budget + 1)
  | map {A B : Type} {budget : Nat} (f : A → B)
      (source : Program oracle A budget) : Program oracle B budget
  | bind {A B : Type} {first second : Nat} (source : Program oracle A first)
      (next : A → Program oracle B second) : Program oracle B (first + second)
  | weaken {A : Type} {first second : Nat} (source : Program oracle A first)
      (bounded : first ≤ second) : Program oracle A second

def Program.run {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : OracleHandler oracle State) : Program oracle A budget → State → A × State
  | .pure value, state => (value, state)
  | .query request next, state =>
    let answer := handler request state
    (next answer.1).run handler answer.2
  | .map f source, state =>
    let answer := source.run handler state
    (f answer.1, answer.2)
  | .bind source next, state =>
    let answer := source.run handler state
    (next answer.1).run handler answer.2
  | .weaken source _, state => source.run handler state

theorem Program.run_bind {oracle : OracleSpec.{0, 0}} {A B State : Type}
    {first second : Nat} (handler : OracleHandler oracle State)
    (source : Program oracle A first) (next : A → Program oracle B second) (state : State) :
    (Program.bind source next).run handler state =
      (next (source.run handler state).1).run handler (source.run handler state).2 := rfl

theorem Program.run_map {oracle : OracleSpec.{0, 0}} {A B State : Type}
    {budget : Nat} (handler : OracleHandler oracle State)
    (f : A → B) (source : Program oracle A budget) (state : State) :
    (Program.map f source).run handler state =
      (f (source.run handler state).1, (source.run handler state).2) := rfl

theorem Program.run_weaken {oracle : OracleSpec.{0, 0}} {A State : Type}
    {first second : Nat} (handler : OracleHandler oracle State)
    (source : Program oracle A first) (bounded : first ≤ second) (state : State) :
    (Program.weaken source bounded).run handler state = source.run handler state := rfl

/-- The execution counter counts actual oracle calls. -/
def Program.runCount {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : OracleHandler oracle State) : Program oracle A budget → State → (A × State) × Nat
  | .pure value, state => ((value, state), 0)
  | .query request next, state =>
    let answer := handler request state
    let tail := (next answer.1).runCount handler answer.2
    (tail.1, tail.2 + 1)
  | .map f source, state =>
    let answer := source.runCount handler state
    ((f answer.1.1, answer.1.2), answer.2)
  | .bind source next, state =>
    let first := source.runCount handler state
    let second := (next first.1.1).runCount handler first.1.2
    (second.1, first.2 + second.2)
  | .weaken source _, state => source.runCount handler state

 theorem Program.runCount_correct {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : OracleHandler oracle State) (program : Program oracle A budget) (state : State) :
    (program.runCount handler state).1 = program.run handler state ∧
      (program.runCount handler state).2 ≤ budget := by
  induction program generalizing state with
  | pure => exact ⟨rfl, Nat.le_refl _⟩
  | query request next inductionHypothesis =>
    obtain ⟨same, count⟩ := inductionHypothesis (handler request state).1 (handler request state).2
    exact ⟨same, Nat.add_le_add_right count 1⟩
  | map f source inductionHypothesis =>
    obtain ⟨same, count⟩ := inductionHypothesis state
    exact ⟨by simp only [Program.runCount, Program.run, same], count⟩
  | bind source next first second =>
    obtain ⟨firstEq, firstCount⟩ := first state
    obtain ⟨secondEq, secondCount⟩ := second
      (source.runCount handler state).1.1 (source.runCount handler state).1.2
    constructor
    · change (Program.runCount handler (next (source.runCount handler state).1.1)
        (source.runCount handler state).1.2).1 = _
      rw [secondEq, firstEq]
      rfl
    · exact Nat.add_le_add firstCount secondCount
  | weaken source bounded inductionHypothesis =>
    exact ⟨(inductionHypothesis state).1, (inductionHypothesis state).2.trans bounded⟩

/-- The command list becomes a bounded oracle program. -/
def commands : (values : List FixedCommand) → Program spec Unit values.length
  | [] => .pure ()
  | command :: rest => .query (.program command) (fun _ => commands rest)

theorem commands_run (values : List FixedCommand) (state : SimulatorState) :
    (commands values).run handler state = ((), executeFixedCommands state values) := by
  induction values generalizing state with
  | nil => rfl
  | cons command rest inductionHypothesis =>
    exact inductionHypothesis (executeFixed state command)

/-- The vector program makes one EncPRF query for each coordinate. -/
def encVector : (count : Nat) →
    (Fin count → EncPRF.PermutationIndex) → (Fin count → Block) →
    Program spec (Fin count → Block) count
  | 0, _, _ => .pure Fin.elim0
  | count + 1, indices, inputs =>
    .query (.read (.encForward (indices 0) (inputs 0))) fun head =>
      Program.map (fun (tail : Fin count → Block) => Fin.cases (motive := fun _ => Block) head tail)
        (encVector count (fun index => indices index.succ) (fun index => inputs index.succ))

theorem encVector_run (count : Nat)
    (indices : Fin count → EncPRF.PermutationIndex) (inputs : Fin count → Block)
    (state : SimulatorState) :
    (encVector count indices inputs).run handler state =
      ((fun index => state.encOracle.permutation (indices index) (inputs index)), state) := by
  induction count with
  | zero =>
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  | succ count inductionHypothesis =>
    simp only [encVector, Program.run, handler, inductionHypothesis]
    apply Prod.ext
    · funext index
      exact Fin.cases rfl (fun _ => rfl) index
    · rfl

/-- This program transforms one coordinate MAC without recording its internal reads. -/
def coordinate (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    Program spec CoordinateMac coordinateBitCount :=
  Program.map (fun values => Vector.ofFn fun index =>
      (values index ^^^ keys.second) ^^^ mac[index.val])
    (encVector coordinateBitCount (fun index => (axis, index))
      (fun index => encodeBit (bits.getLsb index) ^^^ keys.first))

theorem coordinate_run (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) (state : SimulatorState) :
    (coordinate keys axis bits mac).run handler state =
      (EncPRF.transformCoordinateMac state.encOracle keys axis bits mac, state) := by
  simp only [coordinate, Program.run, encVector_run]
  rfl

/-- The linking program uses one hash query and 508 permutation queries. -/
def link (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    Program spec InputMac 509 :=
  .query (.read (.hash (curve.result input))) fun hash =>
    let keys : WhiteningKeys := ⟨hash.1, hash.2⟩
    Program.bind (coordinate keys .x (BitInput.ofAffine input).xBits mac.x) (fun x =>
      Program.map (fun y => (⟨x, y⟩ : InputMac))
        (coordinate keys .y (BitInput.ofAffine input).yBits mac.y))

theorem link_run (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (state : SimulatorState) :
    (link curve input mac).run handler state = (linkedPointInputMac state curve input mac, state) := by
  simp only [link, Program.run, handler, coordinate_run]
  rfl

/-- The distribution semantics compiles the executable syntax into the existing oracle language. -/
noncomputable def Program.toOracle {oracle : OracleSpec.{0, 0}} {A : Type} {budget : Nat} :
    Program oracle A budget → OracleProgram oracle A budget
  | .pure value => .pure (PMF.pure value)
  | .query request next => .query request (fun answer => (next answer).toOracle)
  | .map f source => ThreePhase.castBudget (Nat.add_zero _)
      (ThreePhase.append (fun value => .pure (budget := 0) (PMF.pure (f value))) source.toOracle)
  | .bind source next => ThreePhase.append (fun value => (next value).toOracle) source.toOracle
  | @Program.weaken _ _ first second source bounded =>
      ThreePhase.castBudget (Nat.add_sub_of_le bounded)
        (ThreePhase.raise (second - first) source.toOracle)

 theorem Program.toOracle_run {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (handler : OracleHandler oracle State) (program : Program oracle A budget) (state : State) :
    program.toOracle.run handler state = PMF.pure (program.run handler state) := by
  induction program generalizing state with
  | pure value => simp only [toOracle, OracleProgram.run_pure, PMF.pure_map]; rfl
  | query request next ih => simpa only [toOracle, OracleProgram.run_query, Program.run] using ih _ _
  | map f source inductionHypothesis =>
    simp only [toOracle, ThreePhase.run_castBudget, ThreePhase.run_append, inductionHypothesis,
      PMF.pure_bind, OracleProgram.run_pure, PMF.pure_map]
    rfl
  | bind source next first second =>
    simp only [toOracle, ThreePhase.run_append, first, PMF.pure_bind, second]
    rfl
  | weaken source bounded inductionHypothesis =>
    simpa only [toOracle, ThreePhase.run_castBudget, ThreePhase.run_raise, Program.run] using
      inductionHypothesis state

/-- The valid path uses the actual link and at most 835914 programming attempts. -/
def validProgram [FieldCertificate] [GroupCertificate] (state : CircuitSimulatorState)
    (input : AffineInput) (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    Program spec Garbling.Labels 836423 :=
  .bind (link (state.selectedCurve input) input (state.labels input).inputMac) fun mac =>
    .map (fun _ => state.labels input)
      (.weaken (commands (scheduleCommands
        (pipelineGateSchedule (state.selectedCurve input) (state.selectedPoints input output free scales)
          input (state.labels input).inputMac mac))) (by
        have bound := scheduleCommands_length
          (pipelineGateSchedule (state.selectedCurve input) (state.selectedPoints input output free scales)
            input (state.labels input).inputMac mac)
        rw [pipelineGateSchedule_length_value] at bound
        exact bound))

theorem validProgram_run [FieldCertificate] [GroupCertificate] (state : CircuitSimulatorState)
    (input : AffineInput) (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    (validProgram state input output free scales).run handler state.oracle =
      (state.labels input, (state.programForOutput input output free scales).oracle) := by
  simp only [validProgram, Program.run_bind, link_run, Program.run_map,
    Program.run_weaken, commands_run, scheduleCommands_correct,
    CircuitSimulatorState.programForOutput, CircuitSimulatorState.selectedSchedule,
    linkedPipelineGateSchedule]

/-- The invalid path programs the curve gates without reading the hidden link. -/
def invalidProgram (state : CircuitSimulatorState) (input : AffineInput) :
    Program spec Garbling.Labels 3810 :=
  .map (fun _ => state.labels input)
    (.weaken (commands (scheduleCommands
      ((state.selectedCurve input).schedule input (state.labels input).inputMac))) (by
      have bound := scheduleCommands_length
        ((state.selectedCurve input).schedule input (state.labels input).inputMac)
      rw [CurveGateRequest.schedule_length] at bound
      exact bound))

 theorem invalidProgram_run (state : CircuitSimulatorState) (input : AffineInput) :
    (invalidProgram state input).run handler state.oracle =
      (state.labels input, programGateSchedule state.oracle
        ((state.selectedCurve input).schedule input (state.labels input).inputMac)) := by
  simp only [invalidProgram, Program.run, commands_run, scheduleCommands_correct]

end SimulatorMachine
end Kriterion.ArgoMAC.Security
