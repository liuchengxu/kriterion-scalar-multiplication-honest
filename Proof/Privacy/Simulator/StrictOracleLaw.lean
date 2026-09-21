import Proof.Privacy.Simulator.PublicOracleLaw
import Proof.Privacy.Distribution.SharedProgrammingDistribution
namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
noncomputable section
set_option maxRecDepth 4096

/-- The strict source stops when a command does not use a fresh pair. -/
def strictCommands {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex] :
    LazyOracle.State FixedIndex EncIndex → List (FixedIndex × Block × Block) →
      Option (LazyOracle.State FixedIndex EncIndex)
  | state, [] => some state
  | state, command :: rest => do
      let updated ← LazyOracle.program (.fixedForward command.1 command.2.1) command.2.2 state
      strictCommands updated rest

private theorem swap_prefix {size : Nat} (used : Nat) (room : used < size)
    (position value : Fin size) (fresh : used ≤ position.val) :
    (Equiv.swap ⟨used, room⟩ position value).val < used + 1 ↔ value.val < used ∨ value = position := by
  by_cases same : value = position
  · subst value
    simp
  · by_cases start : value = ⟨used, room⟩
    · subst value
      have unequal : used ≠ position.val := by
        intro equal
        apply same
        exact Fin.ext equal
      simp only [Equiv.swap_apply_left, lt_self_iff_false, false_or]
      constructor
      · intro bounded
        exfalso
        omega
      · intro equal
        exact (same equal).elim
    · rw [Equiv.swap_apply_of_ne_of_ne start same]
      have unequal : value.val ≠ used := fun equal => start (Fin.ext equal)
      simp only [same, or_false]
      omega

theorem SparsePermutation.extend_knownInput {size : Nat} (state : SparsePermutation size)
    (room : state.used < size) (input output value : Fin size)
    (fresh : state.used ≤ input.val) :
    (state.extend room input output).knownInput value ↔
      state.knownInput value ∨ value = state.input input := by
  simpa only [SparsePermutation.knownInput, SparsePermutation.extend, SparsePermutation.input,
    swaps, Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.eq_symm_apply, eq_comm] using
    swap_prefix state.used room input (state.input.symm value) fresh

theorem SparsePermutation.extend_knownOutput {size : Nat} (state : SparsePermutation size)
    (room : state.used < size) (input output value : Fin size)
    (fresh : state.used ≤ output.val) :
    (state.extend room input output).knownOutput value ↔
      state.knownOutput value ∨ value = state.output output := by
  simpa only [SparsePermutation.knownOutput, SparsePermutation.extend, SparsePermutation.output,
    swaps, Equiv.symm_trans_apply, Equiv.symm_swap, Equiv.eq_symm_apply, eq_comm] using
    swap_prefix state.used room output (state.output.symm value) fresh

/-- The ghost transcript contains exactly the fixed oracle's used domains and ranges. -/
def HistoryMatches {FixedIndex EncIndex : Type} (state : LazyOracle.State FixedIndex EncIndex)
    (history : List (PermutationRecord FixedIndex Block)) : Prop :=
  (∀ index input, (state.fixed index).knownInput input.toFin ↔
    ∃ record ∈ history, record.index = index ∧ record.domain = input) ∧
  (∀ index output, (state.fixed index).knownOutput output.toFin ↔
    ∃ record ∈ history, record.index = index ∧ record.range = output)

theorem HistoryMatches.fresh {FixedIndex EncIndex : Type}
    {state : LazyOracle.State FixedIndex EncIndex} {history : List (PermutationRecord FixedIndex Block)}
    (matching : HistoryMatches state history) (index : FixedIndex) (input output : Block) :
    FreshPermutationPair history index input output ↔
      ¬ (state.fixed index).knownInput input.toFin ∧ ¬ (state.fixed index).knownOutput output.toFin := by
  constructor
  · intro fresh
    constructor
    · intro used
      obtain ⟨record, member, same, value⟩ := (matching.1 index input).mp used
      exact (fresh record member same).1 value
    · intro used
      obtain ⟨record, member, same, value⟩ := (matching.2 index output).mp used
      exact (fresh record member same).2 value
  · rintro ⟨domain, range⟩ record member same
    constructor
    · intro value
      exact domain ((matching.1 index input).mpr ⟨record, member, same, value⟩)
    · intro value
      exact range ((matching.2 index output).mpr ⟨record, member, same, value⟩)

theorem history_program {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]
    {state updated : LazyOracle.State FixedIndex EncIndex} {history : List (PermutationRecord FixedIndex Block)}
    (matching : HistoryMatches state history) (index : FixedIndex) (input output : Block)
    (success : LazyOracle.program (.fixedForward index input) output state = some updated) :
    HistoryMatches updated (PermutationRecord.mk .program .simulator index input output :: history) := by
  simp only [LazyOracle.program, Option.map_eq_some_iff] at success
  obtain ⟨next, installed, rfl⟩ := success
  unfold LazyOracle.permutationProgram at installed
  split at installed
  · rename_i fresh
    cases installed
    constructor
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [SparsePermutation.extend_knownInput _ _ _ _ _ (Nat.le_of_not_gt fresh.1)]
        simp [matching.1, Equiv.apply_symm_apply, or_comm, eq_comm]
        rw [BitVec.toFin_inj]
      · simp [Function.update_of_ne same, matching.1, Ne.symm same]
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [SparsePermutation.extend_knownOutput _ _ _ _ _ (Nat.le_of_not_gt fresh.2)]
        simp [matching.2, Equiv.apply_symm_apply, or_comm, eq_comm]
        rw [BitVec.toFin_inj]
      · simp [Function.update_of_ne same, matching.2, Ne.symm same]
  · contradiction

theorem strictCommands_fresh {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (history : List (PermutationRecord FixedIndex Block))
    (commands : List (FixedIndex × Block × Block)) (matching : HistoryMatches state history)
    (fresh : FreshRecordSchedule history (commands.map (fun command =>
      PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2))) :
    (strictCommands state commands).isSome = true := by
  induction commands generalizing state history with
  | nil => rfl
  | cons command rest ih =>
      have valid := (matching.fresh command.1 command.2.1 command.2.2).mp fresh.1
      have existsNext : ∃ next, LazyOracle.program (.fixedForward command.1 command.2.1) command.2.2 state = some next := by
        simp [LazyOracle.program, LazyOracle.permutationProgram, valid]
      obtain ⟨next, success⟩ := existsNext
      simp only [strictCommands, success]
      exact ih next _ (history_program matching _ _ _ success) fresh.2

/-- The eager source applies the same command list in the same order. -/
def eagerCommands {FixedIndex EncIndex : Type} [DecidableEq FixedIndex]
    (oracle : PublicOracle FixedIndex EncIndex) (commands : List (FixedIndex × Block × Block)) :
    PublicOracle FixedIndex EncIndex :=
  commands.foldl (fun current command => programFixedOracle command.1 command.2.1 command.2.2 current) oracle

theorem strictCommands_completion {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state updated : LazyOracle.State FixedIndex EncIndex) (commands : List (FixedIndex × Block × Block))
    (success : strictCommands state commands = some updated) :
    (publicCompletion state).map (fun oracle => eagerCommands oracle commands) = publicCompletion updated := by
  induction commands generalizing state with
  | nil =>
      cases success
      change (publicCompletion updated).map id = _
      exact PMF.map_id _
  | cons command rest ih =>
      simp only [strictCommands, bind, Option.bind_eq_some_iff] at success
      obtain ⟨next, installed, success⟩ := success
      have law := congrArg (PMF.map (fun oracle => eagerCommands oracle rest))
        (public_program_fixed state next command.1 command.2.1 command.2.2 installed)
      rw [ih next success] at law
      simpa [eagerCommands, PMF.map_comp, Function.comp_def] using law

theorem strictCommands_history {FixedIndex EncIndex : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state updated : LazyOracle.State FixedIndex EncIndex) (history : List (PermutationRecord FixedIndex Block))
    (commands : List (FixedIndex × Block × Block)) (matching : HistoryMatches state history)
    (success : strictCommands state commands = some updated) :
    HistoryMatches updated (programRecordHistory history (commands.map (fun command =>
      PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2))) := by
  induction commands generalizing state history with
  | nil => cases success; exact matching
  | cons command rest ih =>
      simp only [strictCommands, bind, Option.bind_eq_some_iff] at success
      obtain ⟨next, installed, success⟩ := success
      exact ih next _ (history_program matching _ _ _ installed) success

theorem SparsePermutation.forward_history {size : Nat} (state : SparsePermutation size)
    (input : Fin size) (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.forward input).distribution.support) (value : Fin size) :
    (answer.2.knownInput value ↔ state.knownInput value ∨ value = input) ∧
    (answer.2.knownOutput value ↔ state.knownOutput value ∨ value = answer.1) := by
  unfold SparsePermutation.forward at member
  dsimp only at member
  split at member
  · rename_i known
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst answer
    constructor
    · have : state.knownInput input := known
      simp_all
    · have : state.knownOutput (state.output (state.input.symm input)) := by
        simpa only [SparsePermutation.knownOutput, Equiv.symm_apply_apply] using known
      simp_all
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    constructor
    · simpa using state.extend_knownInput _ _ _ value (Nat.le_of_not_gt fresh)
    · exact state.extend_knownOutput _ _ _ value (by simp [SparsePermutation.suffix])

theorem SparsePermutation.inverse_history {size : Nat} (state : SparsePermutation size)
    (output : Fin size) (answer : Fin size × SparsePermutation size)
    (member : answer ∈ (state.inverse output).distribution.support) (value : Fin size) :
    (answer.2.knownInput value ↔ state.knownInput value ∨ value = answer.1) ∧
    (answer.2.knownOutput value ↔ state.knownOutput value ∨ value = output) := by
  unfold SparsePermutation.inverse at member
  dsimp only at member
  split at member
  · rename_i known
    simp only [Draw.distribution, PMF.mem_support_pure_iff] at member
    subst answer
    constructor
    · have : state.knownInput (state.input (state.output.symm output)) := by
        simpa only [SparsePermutation.knownInput, Equiv.symm_apply_apply] using known
      simp_all
    · have : state.knownOutput output := known
      simp_all
  · rename_i fresh
    obtain ⟨rank, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    rw [← same]
    constructor
    · exact state.extend_knownInput _ _ _ value (by simp [SparsePermutation.suffix])
    · simpa using state.extend_knownOutput _ _ _ value (Nat.le_of_not_gt fresh)

/-- Each public fixed query adds its pair to the ghost history. -/
def queryHistory {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (answer : request.Answer) (history : List (PermutationRecord FixedIndex Block)) :
    List (PermutationRecord FixedIndex Block) :=
  match request with
  | .fixedForward index input => ⟨.forward, .adversary, index, input, answer⟩ :: history
  | .fixedInverse index output => ⟨.inverse, .adversary, index, answer, output⟩ :: history
  | _ => history

theorem history_query {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]
    {state : LazyOracle.State FixedIndex EncIndex} {history : List (PermutationRecord FixedIndex Block)}
    (matching : HistoryMatches state history) (request : PublicQuery FixedIndex EncIndex)
    (answer : request.Answer × LazyOracle.State FixedIndex EncIndex)
    (member : answer ∈ (LazyOracle.query request state).support) :
    HistoryMatches answer.2 (queryHistory request answer.1 history) := by
  cases request with
  | fixedForward index input =>
    obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have known := (state.fixed index).forward_history input.toFin result supported
    constructor
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [(known value.toFin).1]
        simp [queryHistory, matching.1, or_comm, eq_comm]
        rw [BitVec.toFin_inj]
      · simp [queryHistory, Function.update_of_ne same, matching.1, Ne.symm same]
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [(known value.toFin).2]
        simp [queryHistory, matching.2, or_comm, eq_comm]
        rw [← BitVec.toFin_inj]
        simp only [eq_comm]
      · simp [queryHistory, Function.update_of_ne same, matching.2, Ne.symm same]
  | fixedInverse index output =>
    obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have known := (state.fixed index).inverse_history output.toFin result supported
    constructor
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [(known value.toFin).1]
        simp [queryHistory, matching.1, or_comm, eq_comm]
        rw [← BitVec.toFin_inj]
        simp only [eq_comm]
      · simp [queryHistory, Function.update_of_ne same, matching.1, Ne.symm same]
    · intro current value
      by_cases same : current = index
      · subst current
        simp only [Function.update_self]
        rw [(known value.toFin).2]
        simp [queryHistory, matching.2, or_comm, eq_comm]
        rw [BitVec.toFin_inj]
      · simp [queryHistory, Function.update_of_ne same, matching.2, Ne.symm same]
  | encForward index input | encInverse index input | hash input =>
    obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact matching

abbrev TrackedState (FixedIndex EncIndex : Type) :=
  LazyOracle.State FixedIndex EncIndex × List (PermutationRecord FixedIndex Block)

/-- The proof records public pairs without changing the fixed oracle. -/
def trackedQuery {FixedIndex EncIndex : Type} [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (request : PublicQuery FixedIndex EncIndex) (state : TrackedState FixedIndex EncIndex) :
    PMF (request.Answer × TrackedState FixedIndex EncIndex) :=
  (LazyOracle.query request state.1).map fun answer =>
    (answer.1, answer.2, queryHistory request answer.1 state.2)

def trackedEager {FixedIndex EncIndex : Type} :
    OracleHandler (publicOracleSpec FixedIndex EncIndex)
      (PublicOracle FixedIndex EncIndex × List (PermutationRecord FixedIndex Block)) :=
  fun request state =>
    let answer := publicAnswer state.1 request
    (answer, state.1, queryHistory request answer state.2)

def trackedCompletion {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    (state : TrackedState FixedIndex EncIndex) :
    PMF (PublicOracle FixedIndex EncIndex × List (PermutationRecord FixedIndex Block)) :=
  (publicCompletion state.1).map (fun oracle => (oracle, state.2))

theorem tracked_step {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (request : PublicQuery FixedIndex EncIndex) (state : TrackedState FixedIndex EncIndex) :
    (trackedCompletion state).map (trackedEager request) =
      (trackedQuery request state).bind (fun answer =>
        (trackedCompletion answer.2).map (fun complete => (answer.1, complete))) := by
  have law := congrArg (PMF.map (fun answer : request.Answer × PublicOracle FixedIndex EncIndex =>
    (answer.1, answer.2, queryHistory request answer.1 state.2))) (public_step request state.1)
  simpa only [trackedCompletion, trackedQuery, trackedEager, PMF.map_comp, PMF.map_bind,
    PMF.bind_map, publicHandler, Function.comp_def, id] using law

theorem tracked_run {FixedIndex EncIndex Result : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : TrackedState FixedIndex EncIndex) :
    (trackedCompletion state).bind (fun complete => program.run trackedEager complete) =
      (runSampled trackedQuery program state).bind (fun result =>
        (trackedCompletion result.2).map (fun complete => (result.1, complete))) :=
  adaptive_joint_law trackedEager trackedQuery trackedCompletion tracked_step program state

theorem history_run {FixedIndex EncIndex Result : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex] {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : TrackedState FixedIndex EncIndex) (matching : HistoryMatches state.1 state.2)
    (result : Result × TrackedState FixedIndex EncIndex)
    (member : result ∈ (runSampled trackedQuery program state).support) :
    HistoryMatches result.2.1 result.2.2 := by
  induction program generalizing state with
  | pure distribution =>
    obtain ⟨value, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact matching
  | query request next ih =>
    obtain ⟨answer, supported, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨draw, drawMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ih draw.1 _ (history_query matching request draw drawMember) member
  | sample distribution next ih =>
    obtain ⟨value, supported, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
    exact ih value _ matching member

theorem tracked_run_erase {FixedIndex EncIndex Result : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex] {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : TrackedState FixedIndex EncIndex) :
    (runSampled trackedQuery program state).map (fun result => (result.1, result.2.1)) =
      LazyOracle.run program state.1 := by
  induction program generalizing state with
  | pure distribution => simp [runSampled, LazyOracle.run, PMF.map_comp, Function.comp_def]
  | query request next ih =>
    simp only [runSampled, trackedQuery, PMF.map_bind, PMF.bind_map, Function.comp_def, ih,
      LazyOracle.run]
  | sample distribution next ih =>
    simp only [runSampled, PMF.map_bind, ih, LazyOracle.run]

theorem history_empty {FixedIndex EncIndex : Type} :
    HistoryMatches (LazyOracle.empty : LazyOracle.State FixedIndex EncIndex) [] := by
  simp [HistoryMatches, LazyOracle.empty, SparsePermutation.empty, SparsePermutation.knownInput,
    SparsePermutation.knownOutput]

private theorem programFixedOracle_eq (state : Shared.Simulator.OracleState)
    (index : Shared.FixedKeyIndex) (input output : Block) :
    programFixedOracle index input output (state.fixedOracle, state.encOracle, state.hashOracle) =
      ((programFixed state index input output).fixedOracle, state.encOracle, state.hashOracle) := by
  simp only [programFixedOracle, programFixed]
  congr 2
  funext current
  by_cases same : current = index
  · subst current
    simp
  · simp [same]

/-- The old checked source uses the same swaps on each fresh shared command. -/
theorem sharedCommands_eager (state : Shared.Simulator.OracleState) (commands : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands)) :
    (let next := Shared.Simulator.commands state commands
     (next.fixedOracle, next.encOracle, next.hashOracle)) =
      eagerCommands (state.fixedOracle, state.encOracle, state.hashOracle)
        (commands.map fun command => (Shared.fixedIndex command.1, command.2.1, command.2.2)) := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    have checked := (freshPermutationPairCheck_eq_true _ _ _ _).mpr fresh.1
    dsimp only [Shared.Simulator.commandRecord] at checked
    have step : Shared.Simulator.execute state command =
        programFixed state (Shared.fixedIndex command.1) command.2.1 command.2.2 := by
      simp only [Shared.Simulator.execute, tryProgramFixed, checked, ite_true]
    change (let next := Shared.Simulator.commands (Shared.Simulator.execute state command) rest
      (next.fixedOracle, next.encOracle, next.hashOracle)) = _
    rw [step, ih _ fresh.2]
    simp only [List.map_cons, eagerCommands, List.foldl_cons]
    rw [programFixedOracle_eq]
    rfl

/-- A fresh source schedule and strict L give the same full completed oracle law. -/
theorem sharedCommands_completion (state : Shared.Simulator.OracleState)
    (lazy updated : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands))
    (success : strictCommands lazy (commands.map fun command =>
      (Shared.fixedIndex command.1, command.2.1, command.2.2)) = some updated) :
    (publicCompletion lazy).map (fun oracle =>
      let next := Shared.Simulator.commands
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands
      (next.fixedOracle, next.encOracle, next.hashOracle)) = publicCompletion updated := by
  have law := strictCommands_completion lazy updated _ success
  rw [← law]
  apply congrArg (publicCompletion lazy).map
  funext oracle
  exact sharedCommands_eager _ commands fresh

theorem shared_public_run {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result budget)
    (state : Shared.Simulator.OracleState) :
    (program.run idealOracleHandler state).map (fun result =>
      (result.1, (result.2.fixedOracle, result.2.encOracle, result.2.hashOracle), result.2.fixedTranscript)) =
    program.run trackedEager ((state.fixedOracle, state.encOracle, state.hashOracle), state.fixedTranscript) := by
  refine OracleProgram.run_project idealOracleHandler trackedEager
    (fun current : Shared.Simulator.OracleState =>
      ((current.fixedOracle, current.encOracle, current.hashOracle), current.fixedTranscript)) ?_ program state
  intro request current
  cases request <;> exact ⟨rfl, rfl⟩

/-- The prefix keeps the old fixed history and the strict oracle in one exact joint law. -/
theorem shared_public_completion {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result budget)
    (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (publicCompletion lazy).bind (fun oracle =>
      (program.run idealOracleHandler
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2}).map
        (fun result => (result.1, (result.2.fixedOracle, result.2.encOracle, result.2.hashOracle), result.2.fixedTranscript))) =
    (runSampled trackedQuery program (lazy, state.fixedTranscript)).bind (fun result =>
      (publicCompletion result.2.1).map (fun oracle => (result.1, oracle, result.2.2))) := by
  have law := tracked_run program (lazy, state.fixedTranscript)
  simp only [trackedCompletion, PMF.map_comp, PMF.bind_map, Function.comp_def] at law
  rw [← law]
  apply PMF.bind_congr
  intro oracle _
  exact shared_public_run program _

/-- The old good schedule always succeeds under strict L and has the same oracle law. -/
theorem sharedCommands_fresh_completion (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : List FixedCommand) (matching : HistoryMatches lazy state.fixedTranscript)
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands)) :
    ∃ updated,
      strictCommands lazy (commands.map fun command =>
        (Shared.fixedIndex command.1, command.2.1, command.2.2)) = some updated ∧
      HistoryMatches updated (programRecordHistory state.fixedTranscript (Shared.Simulator.commandRecords commands)) ∧
      (publicCompletion lazy).map (fun oracle =>
        let next := Shared.Simulator.commands
          {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands
        (next.fixedOracle, next.encOracle, next.hashOracle)) = publicCompletion updated := by
  let mapped := commands.map (fun command => (Shared.fixedIndex command.1, command.2.1, command.2.2))
  have records : mapped.map (fun command =>
      PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2) =
      Shared.Simulator.commandRecords commands := by
    simp [mapped, Shared.Simulator.commandRecords, Shared.Simulator.commandRecord, List.map_map]
  have success := strictCommands_fresh lazy state.fixedTranscript mapped matching (records ▸ fresh)
  obtain ⟨updated, installed⟩ := Option.isSome_iff_exists.mp success
  refine ⟨updated, installed, ?_, sharedCommands_completion state lazy updated commands fresh installed⟩
  rw [← records]
  exact strictCommands_history lazy updated state.fixedTranscript mapped matching installed

theorem shared_public_result {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result budget)
    (state : Shared.Simulator.OracleState) :
    (program.run idealOracleHandler state).map Prod.fst =
      (program.run (publicHandler id) (state.fixedOracle, state.encOracle, state.hashOracle)).map Prod.fst := by
  have project := OracleProgram.run_project idealOracleHandler (publicHandler id)
    (fun current : Shared.Simulator.OracleState =>
      (current.fixedOracle, current.encOracle, current.hashOracle))
    (by intro request current; cases request <;> exact ⟨rfl, rfl⟩) program state
  have law := congrArg (PMF.map Prod.fst) project
  simpa only [PMF.map_comp, Function.comp_def] using law

/-- Each fresh source schedule gives the same complete adaptive decision law. -/
theorem sharedCommands_postquery {Result : Type} {budget : Nat}
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Result budget)
    (state : Shared.Simulator.OracleState)
    (lazy updated : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands))
    (success : strictCommands lazy (commands.map fun command =>
      (Shared.fixedIndex command.1, command.2.1, command.2.2)) = some updated) :
    (publicCompletion lazy).bind (fun oracle =>
      (program.run idealOracleHandler (Shared.Simulator.commands
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands)).map Prod.fst) =
      (LazyOracle.run program updated).map Prod.fst := by
  have law := congrArg (fun distribution => distribution.bind (fun oracle =>
    (program.run (publicHandler id) oracle).map Prod.fst))
    (sharedCommands_completion state lazy updated commands fresh success)
  simp only [PMF.bind_map, Function.comp_def] at law
  rw [public_run_result] at law
  calc
    _ = _ := ?_
    _ = _ := law
  apply PMF.bind_congr
  intro oracle _
  exact shared_public_result program _

theorem strictCommands_success_fresh {FixedIndex EncIndex : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state updated : LazyOracle.State FixedIndex EncIndex) (history : List (PermutationRecord FixedIndex Block))
    (commands : List (FixedIndex × Block × Block)) (matching : HistoryMatches state history)
    (success : strictCommands state commands = some updated) :
    FreshRecordSchedule history (commands.map (fun command =>
      PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2)) := by
  induction commands generalizing state history with
  | nil => trivial
  | cons command rest ih =>
    simp only [strictCommands, bind, Option.bind_eq_some_iff] at success
    obtain ⟨next, installed, success⟩ := success
    have fresh : ¬ (state.fixed command.1).knownInput command.2.1.toFin ∧
        ¬ (state.fixed command.1).knownOutput command.2.2.toFin := by
      simp only [LazyOracle.program, Option.map_eq_some_iff] at installed
      obtain ⟨permutation, programmed, equal⟩ := installed
      unfold LazyOracle.permutationProgram at programmed
      split at programmed
      · assumption
      · contradiction
    exact ⟨(matching.fresh _ _ _).mpr fresh,
      ih next _ (history_program matching _ _ _ installed) success⟩

theorem sharedCommands_bad_fresh (state : Shared.Simulator.OracleState) (commands : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands)) :
    (Shared.Simulator.commands state commands).bad = state.bad := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    have checked := (freshPermutationPairCheck_eq_true _ _ _ _).mpr fresh.1
    dsimp only [Shared.Simulator.commandRecord] at checked
    have step : Shared.Simulator.execute state command =
        programFixed state (Shared.fixedIndex command.1) command.2.1 command.2.2 := by
      simp only [Shared.Simulator.execute, tryProgramFixed, checked, ite_true]
    change (Shared.Simulator.commands (Shared.Simulator.execute state command) rest).bad = _
    rw [step, ih _ fresh.2]
    rfl

theorem sharedCommands_fresh_of_not_bad (state : Shared.Simulator.OracleState) (commands : List FixedCommand)
    (good : (Shared.Simulator.commands state commands).bad = false) :
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands) := by
  induction commands generalizing state with
  | nil => trivial
  | cons command rest ih =>
    have stepGood := Shared.Simulator.commands_priorGood (Shared.Simulator.execute state command) rest good
    have checked : freshPermutationPairCheck state.fixedTranscript
        (Shared.fixedIndex command.1) command.2.1 command.2.2 = true := by
      by_contra failed
      simp [Shared.Simulator.execute, tryProgramFixed, failed, markBad] at stepGood
    have step : Shared.Simulator.execute state command =
        programFixed state (Shared.fixedIndex command.1) command.2.1 command.2.2 := by
      simp only [Shared.Simulator.execute, tryProgramFixed, checked, ite_true]
    refine ⟨(freshPermutationPairCheck_eq_true _ _ _ _).mp checked, ?_⟩
    rw [Shared.Simulator.commands, step] at good
    exact ih _ good

/-- Strict L fails exactly when the old checked command source reports a used pair. -/
theorem sharedCommands_strict_failure (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : List FixedCommand) (matching : HistoryMatches lazy state.fixedTranscript)
    (initial : state.bad = false) :
    strictCommands lazy (commands.map fun command =>
      (Shared.fixedIndex command.1, command.2.1, command.2.2)) = none ↔
      (Shared.Simulator.commands state commands).bad = true := by
  constructor
  · intro failed
    by_contra notBad
    have fresh := sharedCommands_fresh_of_not_bad state commands (Bool.eq_false_of_not_eq_true notBad)
    obtain ⟨updated, success, _, _⟩ := sharedCommands_fresh_completion state lazy commands matching fresh
    rw [failed] at success
    contradiction
  · intro bad
    cases success : strictCommands lazy (commands.map fun command =>
        (Shared.fixedIndex command.1, command.2.1, command.2.2)) with
    | none => rfl
    | some updated =>
      have fresh := strictCommands_success_fresh lazy updated state.fixedTranscript _ matching success
      have records : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands) := by
        simp only [List.map_map, Function.comp_def] at fresh
        exact fresh
      have good := (sharedCommands_bad_fresh state commands records).trans initial
      rw [bad] at good
      contradiction

/-- Strict programming and the final adaptive phase match the checked source on all samples. -/
theorem sharedCommands_strict_postquery {budget : Nat}
    (program : OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Bool budget)
    (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : List FixedCommand) (matching : HistoryMatches lazy state.fixedTranscript)
    (initial : state.bad = false) :
    (publicCompletion lazy).bind (fun oracle =>
      let next := Shared.Simulator.commands
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands
      if next.bad then PMF.pure false else (program.run idealOracleHandler next).map Prod.fst) =
    match strictCommands lazy (commands.map fun command =>
      (Shared.fixedIndex command.1, command.2.1, command.2.2)) with
    | none => PMF.pure false
    | some updated => (LazyOracle.run program updated).map Prod.fst := by
  cases success : strictCommands lazy (commands.map fun command =>
      (Shared.fixedIndex command.1, command.2.1, command.2.2)) with
  | none =>
    have bad (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
        (Shared.Simulator.commands {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands).bad = true :=
      (sharedCommands_strict_failure
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2}
        lazy commands matching initial).mp success
    simp only [bad, if_true]
    exact PMF.bind_const _ _
  | some updated =>
    have fresh := strictCommands_success_fresh lazy updated state.fixedTranscript _ matching success
    have records : FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords commands) := by
      simp only [List.map_map, Function.comp_def] at fresh
      exact fresh
    have good (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
        (Shared.Simulator.commands {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2} commands).bad = false :=
      (sharedCommands_bad_fresh
        {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2}
        commands records).trans initial
    simp only [good, Bool.false_eq_true, if_false]
    exact sharedCommands_postquery program state lazy updated commands records success

theorem strictCommands_append {FixedIndex EncIndex : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (state : LazyOracle.State FixedIndex EncIndex) (first second : List (FixedIndex × Block × Block)) :
    strictCommands state (first ++ second) =
      (strictCommands state first).bind (fun updated => strictCommands updated second) := by
  induction first generalizing state with
  | nil => rfl
  | cons command rest ih =>
    simp only [List.cons_append, strictCommands, bind]
    cases LazyOracle.program (.fixedForward command.1 command.2.1) command.2.2 state with
    | none => rfl
    | some updated => exact ih updated
end
end Kriterion.ArgoMAC.Security.OperationalOracle
