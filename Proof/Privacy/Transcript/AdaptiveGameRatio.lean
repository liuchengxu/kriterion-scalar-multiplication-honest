import Proof.Privacy.Transcript.AdaptiveTranscript
import Proof.Privacy.Transcript.EncPRFGame
import Proof.Privacy.Source.AdaptivePermutationRatio

namespace Kriterion.ArgoMAC.Security

open Cryptography
open scoped ENNReal

noncomputable section

local instance : DecidablePred (fun p : Prop => p) := Classical.propDecidable

/-- The oracle state follows the requests in the transcript. -/
def transcriptFinalState {oracle : OracleSpec.{0, 0}} {State : Type}
    (handler : OracleHandler oracle State) : State → List (Sigma oracle.Answer) → State
  | state, [] => state
  | state, entry :: tail => transcriptFinalState handler (handler entry.1 state).2 tail

/-- The public transcript determines the final oracle state. -/
theorem runTranscript_finalState {oracle : OracleSpec.{0, 0}} {State Result : Type}
    (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    output.2.1 = transcriptFinalState handler state output.2.2 := by
  induction program generalizing state output with
  | pure distribution =>
      simp only [runOracleProgramWithTranscript_pure, PMF.mem_support_map_iff] at member
      obtain ⟨value, _, rfl⟩ := member
      rfl
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_query, PMF.mem_support_map_iff] at member
      obtain ⟨value, valueMember, rfl⟩ := member
      exact inductionHypothesis _ _ value valueMember
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.mem_support_bind_iff] at member
      obtain ⟨value, _, valueMember⟩ := member
      exact inductionHypothesis value state output valueMember

/-- This law removes the final state from a fixed transcript mass. -/
theorem runTranscript_full_mass {oracle : OracleSpec.{0, 0}} {State Result : Type}
    (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state finalState : State)
    (result : Result) (transcript : List (Sigma oracle.Answer)) :
    (runOracleProgramWithTranscript handler program state) (result, finalState, transcript) =
      if finalState = transcriptFinalState handler state transcript then
        ((runOracleProgramWithTranscript handler program state).map
          (fun output => (output.1, output.2.2))) (result, transcript)
      else 0 := by
  classical
  by_cases same : finalState = transcriptFinalState handler state transcript
  · rw [if_pos same, PMF.map_apply]
    rw [tsum_eq_single (result, finalState, transcript)]
    · simp
    · intro output different
      by_cases member : output ∈ (runOracleProgramWithTranscript handler program state).support
      · have final := runTranscript_finalState handler program state output member
        by_cases equal : (result, transcript) = (output.1, output.2.2)
        · have first := congrArg Prod.fst equal
          have tail := congrArg Prod.snd equal
          have states : output.2.1 = finalState := by rw [final, ← tail, ← same]
          have : output = (result, finalState, transcript) := by
            rcases output with ⟨value, last, history⟩
            simp_all
          exact False.elim (different this)
        · simp [equal]
      · have zero : (runOracleProgramWithTranscript handler program state) output = 0 := by
          rwa [PMF.apply_eq_zero_iff]
        simp [zero]
  · rw [if_neg same, PMF.apply_eq_zero_iff]
    intro member
    exact same (runTranscript_finalState handler program state _ member)

/-- A fixed first transcript fixes the state of the continuation. -/
theorem runTranscript_bind_mass {oracle : OracleSpec.{0, 0}} {State Result Next : Type}
    (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State)
    (next : Result × State × List (Sigma oracle.Answer) → PMF Next)
    (result : Result) (transcript : List (Sigma oracle.Answer)) (value : Next) :
    ((runOracleProgramWithTranscript handler program state).bind fun output =>
      (next output).map fun item => (output.1, output.2.2, item))
        (result, transcript, value) =
    ((runOracleProgramWithTranscript handler program state).map
      (fun output => (output.1, output.2.2))) (result, transcript) *
        next (result, transcriptFinalState handler state transcript, transcript) value := by
  classical
  rw [PMF.bind_apply]
  rw [tsum_eq_single (result, transcriptFinalState handler state transcript, transcript)]
  · rw [runTranscript_full_mass, if_pos rfl]
    congr 1
    simp only [PMF.map_apply, Prod.mk.injEq, true_and]
    rw [tsum_eq_single value]
    · simp
    · intro item different
      simp [Ne.symm different]
  · intro output different
    by_cases member : output ∈ (runOracleProgramWithTranscript handler program state).support
    · have final := runTranscript_finalState handler program state output member
      have differentTag : ¬ (output.1 = result ∧ output.2.2 = transcript) := by
        rintro ⟨first, tail⟩
        apply different
        rcases output with ⟨item, last, history⟩
        simp_all
      simp only [PMF.map_apply, Prod.mk.injEq]
      have zero : ∀ item : Next,
          ¬ (result = output.1 ∧ transcript = output.2.2 ∧ value = item) := by
        intro item same
        exact differentTag ⟨same.1.symm, same.2.1.symm⟩
      simp [zero]
    · have zero : (runOracleProgramWithTranscript handler program state) output = 0 := by
        rwa [PMF.apply_eq_zero_iff]
      rw [zero, zero_mul]

/-- This experiment keeps the selected adversary state in its transcript. -/
def twoPhaseTranscript {oracle : OracleSpec.{0, 0}} {State First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (choose : OracleProgram oracle First firstBudget)
    (encode : State → First → PMF (Labels × State))
    (decide : First → Labels → OracleProgram oracle Second secondBudget)
    (state : State) : PMF (First × List (Sigma oracle.Answer) ×
      Labels × Second × List (Sigma oracle.Answer)) :=
  (runOracleProgramWithTranscript handler choose state).bind fun selected =>
    ((encode selected.2.1 selected.1).bind fun encoded =>
      (runOracleProgramWithTranscript handler (decide selected.1 encoded.1) encoded.2).map
        fun decided => (encoded.1, decided.1, decided.2.2)).map
          fun result => (selected.1, selected.2.2, result)

/-- The first transcript separates from the encoding and second phase. -/
theorem twoPhaseTranscript_first_mass {oracle : OracleSpec.{0, 0}} {State First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (choose : OracleProgram oracle First firstBudget)
    (encode : State → First → PMF (Labels × State))
    (decide : First → Labels → OracleProgram oracle Second secondBudget)
    (state : State) (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer)) :
    twoPhaseTranscript handler choose encode decide state
      (selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript handler choose state).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((encode (transcriptFinalState handler state before) selected).bind fun encoded =>
      (runOracleProgramWithTranscript handler (decide selected encoded.1) encoded.2).map
        fun decided => (encoded.1, decided.1, decided.2.2)) (labels, decision, after) := by
  exact runTranscript_bind_mass handler choose state _ selected before (labels, decision, after)

/-- This map removes only the selected private adversary state. -/
def publicTwoPhaseTranscript {oracle : OracleSpec.{0, 0}} {Input Public Labels Aux : Type}
    (table : Public) (output : (Input × Aux) × List (Sigma oracle.Answer) ×
      Labels × Bool × List (Sigma oracle.Answer)) : AdaptiveTranscript oracle Input Public Labels :=
  ⟨table, output.1.1, output.2.2.1, output.2.1, output.2.2.2.2, output.2.2.2.1⟩

/-- The real endpoint is the public map of the two-phase experiment. -/
theorem realAdaptiveTranscript_twoPhase
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (handler : OracleHandler oracle Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    realAdaptiveTranscript scheme randomTape handler adversary parameter circuit auxiliary =
      (randomTape parameter).bind fun randomness =>
        let garbled := scheme.garble parameter circuit randomness
        (twoPhaseTranscript handler
          (adversary.chooseInput parameter garbled.1 auxiliary)
          (fun state selected => PMF.pure (scheme.encode garbled.2 selected.1, state))
          (fun selected labels => adversary.decide parameter garbled.1 labels auxiliary selected.2)
          randomness).map (publicTwoPhaseTranscript garbled.1) := by
  simp only [realAdaptiveTranscript, twoPhaseTranscript, PMF.map_bind, PMF.pure_bind,
    PMF.map_comp, Function.comp_def, publicTwoPhaseTranscript]

/-- The ideal endpoint uses the same two-phase observation map. -/
theorem idealAdaptiveTranscript_twoPhase
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Topology State Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
    (handler : OracleHandler oracle State)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    idealAdaptiveTranscript scheme topology simulator handler adversary parameter circuit auxiliary =
      (simulator.simulateGarble parameter (topology circuit)).bind fun simulated =>
        (twoPhaseTranscript handler
          (adversary.chooseInput parameter simulated.1 auxiliary)
          (fun state selected => simulator.simulateEncode state selected.1
            (scheme.function circuit selected.1))
          (fun selected labels => adversary.decide parameter simulated.1 labels auxiliary selected.2)
          simulated.2).map (publicTwoPhaseTranscript simulated.1) := by
  simp only [idealAdaptiveTranscript, twoPhaseTranscript, PMF.map_bind, PMF.map_comp,
    Function.comp_def, publicTwoPhaseTranscript]

/-- This source mass contains only oracle and encoding constraints. -/
def twoPhaseSourceMass {oracle : OracleSpec.{0, 0}} {State First Labels : Type}
    (handler : OracleHandler oracle State)
    (encode : State → First → PMF (Labels × State)) (state : State)
    (selected : First) (labels : Labels) (before after : List (Sigma oracle.Answer)) : ℝ≥0∞ :=
  if OracleTranscriptCompatible handler state before then
    (encode (transcriptFinalState handler state before) selected).toOuterMeasure
      {encoded | encoded.1 = labels ∧ OracleTranscriptCompatible handler encoded.2 after}
  else 0

/-- Both adversary phases separate from the exact source constraints. -/
theorem twoPhaseTranscript_mass_factor {oracle : OracleSpec.{0, 0}}
    {State First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (choose : OracleProgram oracle First firstBudget)
    (encode : State → First → PMF (Labels × State))
    (decide : First → Labels → OracleProgram oracle Second secondBudget)
    (state referenceBefore referenceAfter : State)
    (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer))
    (firstCompatible : OracleTranscriptCompatible handler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible handler referenceAfter after) :
    twoPhaseTranscript handler choose encode decide state
      (selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript handler choose referenceBefore).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript handler (decide selected labels) referenceAfter).map
      (fun output => (output.1, output.2.2))) (decision, after) *
    twoPhaseSourceMass handler encode state selected labels before after := by
  rw [twoPhaseTranscript_first_mass]
  rw [selectedProgram_transcript_mass_factor handler (decide selected)
    (encode (transcriptFinalState handler state before) selected) Prod.fst Prod.snd
    referenceAfter labels decision after secondCompatible]
  by_cases compatible : OracleTranscriptCompatible handler state before
  · rw [runOracleProgramWithTranscript_mass_eq handler handler choose state referenceBefore
      selected before compatible firstCompatible]
    simp only [twoPhaseSourceMass, compatible, if_true, mul_assoc]
  · rw [runOracleProgramWithTranscript_mass_zero handler choose state selected before compatible]
    simp [twoPhaseSourceMass, compatible]

/-- This experiment samples the retained source before both adversary phases. -/
def sampledTwoPhaseTranscript {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → PMF (Labels × State))
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget) :=
  samples.bind fun source =>
    (twoPhaseTranscript handler (choose (table source)) (encode source)
      (decide (table source)) (state source)).map (Prod.mk (table source))

/-- This mass retains the sampled table and every encoding constraint. -/
def sampledTwoPhaseSourceMass {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels : Type}
    (handler : OracleHandler oracle State) (samples : PMF Source)
    (table : Source → Public) (state : Source → State)
    (encode : Source → State → First → PMF (Labels × State))
    (publicTable : Public) (selected : First) (labels : Labels)
    (before after : List (Sigma oracle.Answer)) : ℝ≥0∞ :=
  ∑' source, samples source * if table source = publicTable then
    twoPhaseSourceMass handler (encode source) (state source) selected labels before after else 0

/-- The sampled endpoint has the common two-phase adversary factor. -/
theorem sampledTwoPhaseTranscript_mass_factor {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → PMF (Labels × State))
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (referenceBefore referenceAfter : State)
    (publicTable : Public) (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer))
    (firstCompatible : OracleTranscriptCompatible handler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible handler referenceAfter after) :
    sampledTwoPhaseTranscript handler samples table state choose encode decide
      (publicTable, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript handler (choose publicTable) referenceBefore).map
      (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript handler (decide publicTable selected labels) referenceAfter).map
      (fun output => (output.1, output.2.2))) (decision, after) *
    sampledTwoPhaseSourceMass handler samples table state encode
      publicTable selected labels before after := by
  classical
  rw [sampledTwoPhaseTranscript, PMF.bind_apply, sampledTwoPhaseSourceMass,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro source
  by_cases same : table source = publicTable
  · have tagged : ∀ distribution : PMF (First × List (Sigma oracle.Answer) ×
          Labels × Second × List (Sigma oracle.Answer)),
        (distribution.map (Prod.mk (table source)))
          (publicTable, selected, before, labels, decision, after) =
        distribution (selected, before, labels, decision, after) := by
      intro distribution
      simp only [PMF.map_apply, same, Prod.mk.injEq, true_and]
      rw [tsum_eq_single (selected, before, labels, decision, after)]
      · simp
      · intro value different
        simp [Ne.symm different]
    rw [tagged, same, if_pos rfl,
      twoPhaseTranscript_mass_factor handler (choose publicTable) (encode source)
        (decide publicTable) (state source) referenceBefore referenceAfter
        selected labels decision before after firstCompatible secondCompatible]
    ac_rfl
  · simp [PMF.map_apply, same, Ne.symm same]

/-- The real transcript keeps the selected private adversary state. -/
def realAdaptiveTranscriptWithState
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (handler : OracleHandler oracle Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :=
  sampledTwoPhaseTranscript handler (randomTape parameter)
    (fun randomness => (scheme.garble parameter circuit randomness).1) id
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun randomness state selected =>
      PMF.pure (scheme.encode (scheme.garble parameter circuit randomness).2 selected.1, state))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)

/-- The ideal transcript keeps the same selected private adversary state. -/
def idealAdaptiveTranscriptWithState
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Topology State Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
    (handler : OracleHandler oracle State)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :=
  sampledTwoPhaseTranscript handler (simulator.simulateGarble parameter (topology circuit))
    Prod.fst Prod.snd (fun table => adversary.chooseInput parameter table auxiliary)
    (fun _ state selected => simulator.simulateEncode state selected.1
      (scheme.function circuit selected.1))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)

/-- The real endpoint removes only the retained adversary state. -/
theorem realAdaptiveTranscriptWithState_erase
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (handler : OracleHandler oracle Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    (realAdaptiveTranscriptWithState scheme randomTape handler adversary parameter circuit auxiliary).map
      (fun output => publicTwoPhaseTranscript output.1 output.2) =
    realAdaptiveTranscript scheme randomTape handler adversary parameter circuit auxiliary := by
  rw [realAdaptiveTranscript_twoPhase]
  simp only [realAdaptiveTranscriptWithState, sampledTwoPhaseTranscript,
    PMF.map_bind, PMF.map_comp, Function.comp_def, id_eq]

/-- The ideal endpoint removes the same retained adversary state. -/
theorem idealAdaptiveTranscriptWithState_erase
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Topology State Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
    (handler : OracleHandler oracle State)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    (idealAdaptiveTranscriptWithState scheme topology simulator handler adversary parameter
      circuit auxiliary).map (fun output => publicTwoPhaseTranscript output.1 output.2) =
    idealAdaptiveTranscript scheme topology simulator handler adversary parameter circuit auxiliary := by
  rw [idealAdaptiveTranscript_twoPhase]
  simp only [idealAdaptiveTranscriptWithState, sampledTwoPhaseTranscript,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A deterministic encoding gives one exact retained-source event. -/
theorem sampledTwoPhaseSourceMass_pure {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels : Type}
    (handler : OracleHandler oracle State) (samples : PMF Source)
    (table : Source → Public) (state : Source → State)
    (encode : Source → State → First → Labels × State)
    (publicTable : Public) (selected : First) (labels : Labels)
    (before after : List (Sigma oracle.Answer)) :
    sampledTwoPhaseSourceMass handler samples table state
      (fun source state selected => PMF.pure (encode source state selected))
      publicTable selected labels before after =
    samples.toOuterMeasure {source | table source = publicTable ∧
      OracleTranscriptCompatible handler (state source) before ∧
      (encode source (transcriptFinalState handler (state source) before) selected).1 = labels ∧
      OracleTranscriptCompatible handler
        (encode source (transcriptFinalState handler (state source) before) selected).2 after} := by
  classical
  rw [sampledTwoPhaseSourceMass, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro source
  simp only [twoPhaseSourceMass, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq,
    Set.indicator_apply]
  by_cases sameTable : table source = publicTable <;>
    by_cases first : OracleTranscriptCompatible handler (state source) before <;>
    by_cases second :
      (encode source (transcriptFinalState handler (state source) before) selected).1 = labels ∧
      OracleTranscriptCompatible handler
        (encode source (transcriptFinalState handler (state source) before) selected).2 after <;>
    simp only [sameTable, first, second, and_true, and_false,
      if_true, if_false, mul_one, mul_zero]

/-- Compatibility composes at the exact state after the first transcript. -/
theorem oracleTranscriptCompatible_append {oracle : OracleSpec.{0, 0}} {State : Type}
    (handler : OracleHandler oracle State) (state : State)
    (before after : List (Sigma oracle.Answer)) :
    OracleTranscriptCompatible handler state (before ++ after) ↔
      OracleTranscriptCompatible handler state before ∧
      OracleTranscriptCompatible handler (transcriptFinalState handler state before) after := by
  induction before generalizing state with
  | nil => simp [OracleTranscriptCompatible, transcriptFinalState]
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      simp only [List.cons_append, OracleTranscriptCompatible, transcriptFinalState,
        inductionHypothesis, and_assoc]

/-- The real encoding preserves the oracle state and joins both histories. -/
theorem sampledTwoPhaseSourceMass_real {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels : Type}
    (handler : OracleHandler oracle State) (samples : PMF Source)
    (table : Source → Public) (state : Source → State) (encode : Source → First → Labels)
    (publicTable : Public) (selected : First) (labels : Labels)
    (before after : List (Sigma oracle.Answer)) :
    sampledTwoPhaseSourceMass handler samples table state
      (fun source current selected => PMF.pure (encode source selected, current))
      publicTable selected labels before after =
    samples.toOuterMeasure {source | table source = publicTable ∧
      encode source selected = labels ∧
      OracleTranscriptCompatible handler (state source) (before ++ after)} := by
  rw [sampledTwoPhaseSourceMass_pure]
  congr 1
  ext source
  simp only [Set.mem_setOf_eq, oracleTranscriptCompatible_append]
  tauto

attribute [local instance] fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- A fresh actual schedule changes only the fixed oracle and its history. -/
theorem programGateSchedule_state (state : SimulatorState) (schedule : List GateDirective)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    (oracle : TranscriptOracle state.fixedTranscript) :
    programGateSchedule {state with fixedOracle := oracle.1} schedule =
      {state with
        fixedOracle := (programTranscriptRecords state.fixedTranscript
          (gateProgramRecords schedule) fresh oracle).1
        fixedTranscript := programRecordHistory state.fixedTranscript (gateProgramRecords schedule)} := by
  have metadata : ∀ record ∈ gateProgramRecords schedule,
      record.action = .program ∧ record.origin = .simulator := by
    intro record member
    obtain ⟨directive, _, member⟩ := List.mem_flatMap.mp member
    have member := List.mem_reverse.mp member
    cases branch : directive.bit <;>
      simp only [GateDirective.programRecords, branch, Bool.false_eq_true, if_false, if_true,
        List.mem_cons, List.not_mem_nil, or_false] at member <;>
      rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩
  rw [programGateSchedule_eq_recordSchedule]
  exact programRecordSchedule_state state (gateProgramRecords schedule) fresh metadata oracle

/-- The actual gate schedule has the exact postquery extension density. -/
theorem programGateSchedule_queryMass_product [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries)) :
    ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
      programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} =
      (∏ index, ((Fintype.card Block -
        (Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) +
          Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
            (programmedDomains (gateProgramRecords schedule)) index))).factorial : ℝ≥0∞) /
              (Fintype.card Block).factorial) /
      (∏ index, ((Fintype.card Block -
        (Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) +
          Fintype.card (FixedQueryDomain state.fixedTranscript index))).factorial : ℝ≥0∞) /
            (Fintype.card Block).factorial) := by
  classical
  have mass := programTranscriptRecords_queryMass_product state.fixedTranscript
    (gateProgramRecords schedule) queries fresh reference
  rw [PMF.toOuterMeasure_map_apply] at mass ⊢
  convert mass using 1
  congr 1
  ext oracle
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [programGateSchedule_state state schedule fresh oracle]

/-- The programmed transcript keeps the original EncPRF and hash constraints. -/
theorem programGateSchedule_transcriptMass
    (state : SimulatorState) (schedule : List GateDirective)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (randomness : Garbling.Randomness)
    (enc : state.encOracle = randomness.encPRFOracle)
    (hash : state.hashOracle = randomness.hashOracle) :
    ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
      programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | OracleTranscriptCompatible idealOracleHandler programmed transcript} =
    if NonFixedTranscriptCompatible randomness transcript then
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
        programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle
            (fixedOracleTranscriptRecords transcript)} else 0 := by
  classical
  have compatible (oracle : TranscriptOracle state.fixedTranscript) :
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule {state with fixedOracle := oracle.1} schedule) transcript ↔
      PermutationTranscriptMatches
        (programGateSchedule {state with fixedOracle := oracle.1} schedule).fixedOracle
          (fixedOracleTranscriptRecords transcript) ∧
      NonFixedTranscriptCompatible randomness transcript := by
    rw [programGateSchedule_state state schedule fresh oracle]
    rw [idealOracleTranscriptCompatible_iff_real
      {state with
        fixedOracle := (programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh oracle).1
        fixedTranscript := programRecordHistory state.fixedTranscript (gateProgramRecords schedule)}
      {randomness with fixedKeyOracle :=
        (programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh oracle).1}
      transcript rfl enc hash, realOracleTranscriptCompatible_iff,
      nonFixedTranscriptCompatible_update]
  by_cases kept : NonFixedTranscriptCompatible randomness transcript
  · rw [if_pos kept]
    simp only [PMF.toOuterMeasure_map_apply]
    congr 1
    ext oracle
    exact (compatible oracle).trans (and_iff_left kept)
  · rw [if_neg kept, PMF.toOuterMeasure_map_apply]
    have empty : (fun oracle : TranscriptOracle state.fixedTranscript =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule) ⁻¹'
        {programmed : SimulatorState |
          OracleTranscriptCompatible idealOracleHandler programmed transcript} = ∅ := by
      ext oracle
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      exact (compatible oracle).trans (by simp [kept])
    rw [empty]
    simp

/-- The source, prefix, and extension factors give the corrected active density. -/
theorem slotSourceExtension_eq (N Q prior residual : Nat) (active : Bool) :
    ((N : ℝ≥0∞) ^ Q)⁻¹ * (((N - prior).factorial : ℝ≥0∞) / N.factorial) *
      ((((N - ((if active then Q else 0) + residual)).factorial : ℝ≥0∞) / N.factorial) /
        (((N - ((if active then Q else 0) + prior)).factorial : ℝ≥0∞) / N.factorial)) =
    if active then activeIdealSlotFactor N Q prior residual else
      ((N : ℝ≥0∞) ^ Q)⁻¹ * ((N - residual).factorial : ℝ≥0∞) / N.factorial := by
  have cancel (a b : ℝ≥0∞) :
      (a / (N.factorial : ℝ≥0∞)) / (b / (N.factorial : ℝ≥0∞)) = a / b := by
    simp only [div_eq_mul_inv]
    exact ENNReal.mul_div_mul_right a b
      (by simp only [ENNReal.inv_ne_zero]; exact ENNReal.natCast_ne_top _)
      (by simp only [ENNReal.inv_ne_top]; exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [cancel]
  cases active
  · simp only [Bool.false_eq_true, if_false, Nat.zero_add, div_eq_mul_inv]
    calc
      _ = ((N : ℝ≥0∞) ^ Q)⁻¹ * (N - residual).factorial *
          (N.factorial : ℝ≥0∞)⁻¹ *
          (((N - prior).factorial : ℝ≥0∞) * ((N - prior).factorial : ℝ≥0∞)⁻¹) := by ring
      _ = _ := by
        rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (ENNReal.natCast_ne_top _), mul_one]
  · simp only [if_true, activeIdealSlotFactor, div_eq_mul_inv]
    ring

/-- The bucket product keeps every active and inactive source factor. -/
theorem sourceExtensionProduct_eq {Index : Type} [Fintype Index]
    (N : Nat) (uses prior residual : Index → Nat) (active : Index → Bool) :
    (∏ index, ((N : ℝ≥0∞) ^ uses index)⁻¹) *
      (∏ index, ((N - prior index).factorial : ℝ≥0∞) / N.factorial) *
      ((∏ index, ((N - ((if active index then uses index else 0) + residual index)).factorial :
          ℝ≥0∞) / N.factorial) /
        (∏ index, ((N - ((if active index then uses index else 0) + prior index)).factorial :
          ℝ≥0∞) / N.factorial)) =
      adaptiveIdealPermutationFactor N uses prior residual active := by
  classical
  simp only [div_eq_mul_inv]
  rw [ENNReal.prod_inv_distrib (by
    intro first _ second _ _
    apply Or.inl
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (by simp only [ENNReal.inv_ne_zero]; exact ENNReal.natCast_ne_top _))]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  simpa only [div_eq_mul_inv] using
    slotSourceExtension_eq N (uses index) (prior index) (residual index) (active index)

/-- The actual schedule gives the corrected factor after source and prefix sampling. -/
theorem programGateSchedule_sourceMass_product [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries))
    (uses : Pipeline.FixedKeyIndex → Nat) (active : Pipeline.FixedKeyIndex → Bool)
    (recordCounts : ∀ index, Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) =
      if active index then uses index else 0) :
    (∏ index, ((Fintype.card Block : ℝ≥0∞) ^ uses index)⁻¹) *
      fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
        programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} =
    adaptiveIdealPermutationFactor (Fintype.card Block) uses
      (fun index => Fintype.card (FixedQueryDomain state.fixedTranscript index))
      (fun index => Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
        (programmedDomains (gateProgramRecords schedule)) index)) active := by
  rw [programGateSchedule_queryMass_product state schedule queries fresh reference]
  simp_rw [recordCounts]
  exact sourceExtensionProduct_eq _ _ _ _ _

/-- The actual programmed source mass satisfies the concrete circuit ratio. -/
theorem circuitProgrammedSource_mass_ratio
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BN254.BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (selected : RawLabelBucket → Bool) (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (publicLabel : RawLabelBucket → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index))
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries))
    (recordCounts : ∀ index, Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) =
      if rawSlotBranch index.slot = selected (rawLabelBucket index) then circuitBucketSize index else 0)
    (residualCounts : ∀ index,
      Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
        (programmedDomains (gateProgramRecords schedule)) index) =
      circuitResidualQueryCount (circuitRawGatePrescription keys slopes lifts tables)
        selected publicLabel transcript index)
    (priorFits : ∀ index, circuitBucketSize index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index +
      circuitResidualQueryCount (circuitRawGatePrescription keys slopes lifts tables)
        selected publicLabel transcript index ≤ Fintype.card Block) :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  rw [programGateSchedule_sourceMass_product state schedule queries fresh reference circuitBucketSize
    (fun index => decide (rawSlotBranch index.slot = selected (rawLabelBucket index)))
    (fun index => by simpa only [decide_eq_true_eq] using recordCounts index)]
  simp_rw [residualCounts]
  exact circuitSharedInactive_adaptiveFactor_mass_ge keys slopes lifts tables selected wire shift
    publicLabel randomness transcript compatible offsetsDistinct referenceActive _ priorFits residualFits

end
end Kriterion.ArgoMAC.Security
