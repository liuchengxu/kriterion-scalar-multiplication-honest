import Proof.Privacy.ConcreteSmallSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open Cryptography.Assumptions

namespace ThreePhase

/-- This operation changes only the type of a query bound. -/
def castBudget {oracle : OracleSpec} {Result : Type} {first second : Nat}
    (equal : first = second) (program : OracleProgram oracle Result first) :
    OracleProgram oracle Result second := equal ▸ program

@[simp] theorem run_castBudget {oracle : OracleSpec} {Result State : Type}
    (handler : OracleHandler oracle State) {first second : Nat} (equal : first = second)
    (program : OracleProgram oracle Result first) (state : State) :
    (castBudget equal program).run handler state = program.run handler state := by
  cases equal
  rfl

/-- This operation increases a program's query bound. -/
def raise {oracle : OracleSpec} {Result : Type} (extra : Nat) :
    {budget : Nat} → OracleProgram oracle Result budget → OracleProgram oracle Result (budget + extra)
  | _, .pure distribution => .pure distribution
  | budget + 1, .query request next =>
      castBudget (Nat.add_right_comm budget extra 1)
        (.query request (fun answer => raise extra (next answer)))
  | _, .sample distribution next => .sample distribution (fun value => raise extra (next value))

/-- This operation runs two oracle programs with one shared state. -/
def append {oracle : OracleSpec} {First Result : Type} {second : Nat}
    (next : First → OracleProgram oracle Result second) :
    {first : Nat} → OracleProgram oracle First first → OracleProgram oracle Result (first + second)
  | budget, .pure distribution =>
      castBudget (Nat.add_comm second budget)
        (.sample distribution (fun value => raise budget (next value)))
  | budget + 1, .query request continuation =>
      castBudget (Nat.add_right_comm budget second 1)
        (.query request (fun answer => append next (continuation answer)))
  | _, .sample distribution continuation =>
      .sample distribution (fun value => append next (continuation value))

@[simp] theorem run_raise {oracle : OracleSpec} {Result State : Type}
    (handler : OracleHandler oracle State) (extra : Nat) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) :
    (raise extra program).run handler state = program.run handler state := by
  induction program generalizing state with
  | pure distribution => simp only [raise, OracleProgram.run_pure]
  | query request next inductionHypothesis =>
      simp only [raise, run_castBudget, OracleProgram.run_query, inductionHypothesis]
  | sample distribution next inductionHypothesis =>
      simp only [raise, OracleProgram.run_sample, inductionHypothesis]

@[simp] theorem run_append {oracle : OracleSpec} {First Result State : Type}
    (handler : OracleHandler oracle State) {first second : Nat}
    (program : OracleProgram oracle First first)
    (next : First → OracleProgram oracle Result second) (state : State) :
    (append next program).run handler state =
      (program.run handler state).bind (fun selected => (next selected.1).run handler selected.2) := by
  induction program generalizing state with
  | pure distribution =>
      simp only [append, run_castBudget, OracleProgram.run_sample, OracleProgram.run_pure, run_raise, PMF.bind_map, Function.comp_def]
  | query request continuation inductionHypothesis =>
      simp only [append, run_castBudget, OracleProgram.run_query, inductionHypothesis]
  | sample distribution continuation inductionHypothesis =>
      simp only [append, OracleProgram.run_sample, inductionHypothesis, PMF.bind_bind]

/-- This adversary has a separate phase before it receives the public circuit. -/
structure Adversary (Aux : Type) where
  Before : Type
  After : Type
  preQueryBudget : Nat → Nat
  inputQueryBudget : Nat → Nat
  decisionQueryBudget : Nat → Nat
  prepare : (parameter : Nat) → Aux →
    OracleProgram Garbling.oracleSpec Before (preQueryBudget parameter)
  chooseInput : (parameter : Nat) → Pipeline.Table → Aux → Before →
    OracleProgram Garbling.oracleSpec (AffineInput × After) (inputQueryBudget parameter)
  decide : (parameter : Nat) → Pipeline.Table → Garbling.Labels → Aux → After →
    OracleProgram Garbling.oracleSpec Bool (decisionQueryBudget parameter)

/-- The compiled adversary delays its first phase until the public circuit arrives. -/
def Adversary.compile {Aux : Type} (adversary : Adversary Aux) :
    GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux where
  State := adversary.After
  firstQueryBudget parameter := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter
  secondQueryBudget := adversary.decisionQueryBudget
  chooseInput parameter table auxiliary :=
    append (adversary.chooseInput parameter table auxiliary) (adversary.prepare parameter auxiliary)
  decide := adversary.decide

/-- The reduction counts all three query phases and one decision step. -/
theorem compile_work {Aux : Type} (adversary : Adversary Aux) (parameter : Nat) :
    GarbledCircuit.adversaryWork adversary.compile parameter =
      adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1 := rfl

/-- The real experiment runs K1 before it constructs and releases the public circuit.
The scalar is fixed before K1. -/
noncomputable def realGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (witness : Garbling.Randomness) : PMF Bool :=
  (randomTape witness parameter).bind fun initial =>
    ((adversary.prepare parameter auxiliary).run Garbling.oracleHandler initial).bind fun prepared =>
      let garbled := (Garbling.garbledCircuit construction).garble parameter scalar prepared.2
      ((adversary.chooseInput parameter garbled.1 auxiliary prepared.1).run
        Garbling.oracleHandler prepared.2).bind fun selected =>
          ((adversary.decide parameter garbled.1
            ((Garbling.garbledCircuit construction).encode garbled.2 selected.1.1)
            auxiliary selected.1.2).run Garbling.oracleHandler selected.2).map Prod.fst

/-- The ideal experiment keeps its hidden coins private during K1.
It releases the public table after K1 and keeps the updated oracle state. -/
noncomputable def idealGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) : PMF Bool :=
  (simulatorStateTape parameter (Garbling.topology scalar)).bind fun initial =>
    ((adversary.prepare parameter auxiliary).run circuitSimulatorOracleHandler initial).bind fun prepared =>
      ((adversary.chooseInput parameter prepared.2.table auxiliary prepared.1).run
        circuitSimulatorOracleHandler prepared.2).bind fun selected =>
          (concreteCircuitSimulator.simulateEncode selected.2 selected.1.1
            ((Garbling.garbledCircuit construction).function scalar selected.1.1)).bind fun encoded =>
              ((adversary.decide parameter prepared.2.table encoded.1 auxiliary selected.1.2).run
                circuitSimulatorOracleHandler encoded.2).map Prod.fst

/-- Every supported run preserves a state projection that each oracle query preserves. -/
theorem run_preserves {oracle : OracleSpec} {Result State View : Type}
    (handler : OracleHandler oracle State) (view : State → View)
    (preserves : ∀ query state, view (handler query state).2 = view state)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State) (member : output ∈ (program.run handler state).support) :
    view output.2 = view state := by
  induction program generalizing state with
  | pure distribution =>
      simp only [OracleProgram.run_pure, PMF.mem_support_map_iff] at member
      obtain ⟨value, _, equal⟩ := member
      cases equal
      rfl
  | query request next inductionHypothesis =>
      rw [OracleProgram.run_query] at member; exact (inductionHypothesis _ _ member).trans (preserves request state)
  | sample distribution next inductionHypothesis =>
      simp only [OracleProgram.run_sample, PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, member⟩ := member
      exact inductionHypothesis value state member

/-- Real queries do not change the random tape. -/
theorem real_run_state {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : Garbling.Randomness)
    (output : Result × Garbling.Randomness)
    (member : output ∈ (program.run Garbling.oracleHandler state).support) : output.2 = state :=
  run_preserves Garbling.oracleHandler id (by intro query state; cases query <;> rfl)
    program state output member

/-- Ideal queries preserve the hidden public table and keep their oracle updates. -/
theorem ideal_run_table {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : CircuitSimulatorState)
    (output : Result × CircuitSimulatorState)
    (member : output ∈ (program.run circuitSimulatorOracleHandler state).support) :
    output.2.table = state.table :=
  run_preserves circuitSimulatorOracleHandler CircuitSimulatorState.table (by intro query state; rfl)
    program state output member

/-- Equal continuations on supported inputs give equal output distributions. -/
theorem bind_eq_on_support {Input Output : Type} (distribution : PMF Input)
    (left right : Input → PMF Output)
    (equal : ∀ input ∈ distribution.support, left input = right input) :
    distribution.bind left = distribution.bind right := by
  ext output
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro input
  by_cases member : input ∈ distribution.support
  · rw [equal input member]
  · have zero : distribution input = 0 := by simpa only [PMF.mem_support_iff, not_not] using member
    simp only [zero, zero_mul]

/-- Delaying K1 until the public circuit arrives preserves the real experiment. -/
theorem realGame_eq_compiled [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (witness : Garbling.Randomness) :
    realGame adversary parameter scalar auxiliary witness =
      GarbledCircuit.realGame (Garbling.garbledCircuit construction) (randomTape witness)
        Garbling.oracleHandler adversary.compile parameter scalar auxiliary := by
  unfold realGame
  generalize Garbling.garbledCircuit construction = scheme
  simp only [GarbledCircuit.realGame, Adversary.compile, run_append, PMF.bind_bind]
  congr 1
  funext initial
  apply bind_eq_on_support
  intro prepared member
  rw [real_run_state (adversary.prepare parameter auxiliary) initial prepared member]

/-- Delaying K1 preserves the ideal table and all oracle state updates. -/
theorem idealGame_eq_compiled [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) :
    idealGame adversary parameter scalar auxiliary =
      GarbledCircuit.idealGame (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary.compile parameter scalar auxiliary := by
  simp only [idealGame, GarbledCircuit.idealGame, concreteCircuitSimulator, circuitSimulator,
    Adversary.compile, PMF.bind_map, Function.comp_def, run_append, PMF.bind_bind]
  congr 1
  funext initial
  apply bind_eq_on_support
  intro prepared member
  rw [ideal_run_table (adversary.prepare parameter auxiliary) initial prepared member]

/-- The original 100-bit theorem covers all three query phases at their exact total cost. -/
theorem concretePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (realGame adversary parameter scalar auxiliary witness)
        (idealGame adversary parameter scalar auxiliary)) := by
  rw [realGame_eq_compiled, idealGame_eq_compiled, ← compile_work]
  exact concreteAdaptivePrivacy witness adversary.compile (fun _ => scalar) (fun _ => auxiliary) parameter

end ThreePhase
end Kriterion.ArgoMAC.Security
