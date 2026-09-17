import Cryptography.Primitives
import VCVio.OracleComp.QueryTracking.Tracing

namespace Kriterion.ArgoMAC.Security

open Cryptography

universe uQuery uAnswer uResult uState uOther

private theorem state_map {σ α β : Type uState} (f : α → β)
    (mx : StateT σ PMF α) (s : σ) :
    (f <$> mx) s = PMF.map (fun p => (f p.1, p.2)) (mx s) := rfl

private theorem state_bind {σ α β : Type uState}
    (mx : StateT σ PMF α) (f : α → StateT σ PMF β) (s : σ) :
    (mx >>= f) s = (mx s).bind (fun p => f p.1 p.2) := rfl

/-- The VCV-io logger records public answers and omits private samples. -/
def transcriptEntry {oracle : OracleSpec.{uQuery, uAnswer}} :
    (request : (OracleProgram.effectSpec.{uQuery, uAnswer, uResult, uState} oracle).Domain) →
    (OracleProgram.effectSpec.{uQuery, uAnswer, uResult, uState} oracle).Range request →
    List (ULift.{max uQuery uAnswer (uResult + 1) uState} (Sigma oracle.Answer))
  | ⟨.query request⟩, answer => [ULift.up ⟨request, answer.down⟩]
  | ⟨.sample _ _⟩, _ => []

/-- VCV-io executes each query and records its public answer in order. -/
noncomputable def runOracleProgramWithTranscript
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State) {budget : Nat}
    (program : OracleProgram oracle Result budget) (state : State) :
    PMF (Result × State × List (Sigma oracle.Answer)) :=
  ((simulateQ ((OracleProgram.implementation.{uQuery, uAnswer, uResult, uState, 0} handler).withTraceAppend
    transcriptEntry) (OracleProgram.toComp program)).run (ULift.up state)).map fun output =>
      (output.1.1.down, output.2.down, output.1.2.map ULift.down)

@[simp] theorem runOracleProgramWithTranscript_pure
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult} {State : Type uState}
    (handler : OracleHandler oracle State) {budget : Nat} (result : PMF Result) (state : State) :
    runOracleProgramWithTranscript handler (.pure (budget := budget) result) state =
      result.map (fun value => (value, state, [])) := by
  simp only [runOracleProgramWithTranscript, OracleProgram.toComp, OracleComp.queryBind,
    simulateQ, PFunctor.FreeM.liftM]
  simp [OracleProgram.implementation, transcriptEntry]
  simp only [state_map, PMF.map_comp, Function.comp_def, List.map_nil]

@[simp] theorem runOracleProgramWithTranscript_query
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult} {State : Type uState}
    (handler : OracleHandler oracle State) {budget : Nat} (request : oracle.Query)
    (next : oracle.Answer request → OracleProgram oracle Result budget) (state : State) :
    runOracleProgramWithTranscript handler (.query request next) state =
      (runOracleProgramWithTranscript handler (next (handler request state).1)
        (handler request state).2).map
        (fun output => (output.1, output.2.1, ⟨request, (handler request state).1⟩ :: output.2.2)) := by
  simp only [runOracleProgramWithTranscript, OracleProgram.toComp, OracleComp.queryBind,
    simulateQ, PFunctor.FreeM.liftM]
  simp [OracleProgram.implementation, transcriptEntry, state_map, state_bind,
    PMF.pure_map, PMF.map_comp, Function.comp_def]

@[simp] theorem runOracleProgramWithTranscript_sample
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result Sample : Type uResult} {State : Type uState}
    (handler : OracleHandler oracle State) {budget : Nat} (distribution : PMF Sample)
    (next : Sample → OracleProgram oracle Result budget) (state : State) :
    runOracleProgramWithTranscript handler (.sample distribution next) state =
      distribution.bind (fun value => runOracleProgramWithTranscript handler (next value) state) := by
  simp only [runOracleProgramWithTranscript, OracleProgram.toComp, OracleComp.queryBind,
    simulateQ, PFunctor.FreeM.liftM]
  simp [OracleProgram.implementation, transcriptEntry, state_map, state_bind,
    PMF.map_comp, PMF.bind_map, PMF.map_bind, Function.comp_def]

/-- The program has the same distribution after transcript erasure. -/
theorem runOracleProgramWithTranscript_erase
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    (runOracleProgramWithTranscript handler program state).map
      (fun output => (output.1, output.2.1)) = program.run handler state := by
  have erased := QueryImpl.fst_map_run_withTraceAppend
    (OracleProgram.implementation.{uQuery, uAnswer, uResult, uState, 0} handler)
    transcriptEntry (OracleProgram.toComp program)
  have evaluated := congrFun erased (ULift.up state)
  simp only [state_map] at evaluated
  have lowered := congrArg (PMF.map (fun output => (output.1.down, output.2.down))) evaluated
  simpa only [runOracleProgramWithTranscript, OracleProgram.run, OracleProgram.execute,
    PMF.map_comp, Function.comp_def] using lowered

/-- A compatible oracle gives each recorded answer in order. -/
def OracleTranscriptCompatible
    {oracle : OracleSpec.{uQuery, uAnswer}} {State : Type uState}
    (handler : OracleHandler oracle State) : State → List (Sigma oracle.Answer) → Prop
  | _, [] => True
  | state, ⟨request, answer⟩ :: tail =>
      (handler request state).1 = answer ∧
        OracleTranscriptCompatible handler (handler request state).2 tail

/-- Each supported transcript is compatible with its oracle. -/
theorem runOracleProgramWithTranscript_compatible
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    OracleTranscriptCompatible handler state output.2.2 := by
  induction program generalizing state output with
  | pure result =>
      simp only [runOracleProgramWithTranscript_pure, PMF.mem_support_map_iff] at member
      rcases member with ⟨value, _, rfl⟩
      trivial
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_query, PMF.mem_support_map_iff] at member
      rcases member with ⟨tailOutput, tailMember, rfl⟩
      exact ⟨rfl, inductionHypothesis _ _ tailOutput tailMember⟩
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.mem_support_bind_iff] at member
      rcases member with ⟨value, _, tailMember⟩
      exact inductionHypothesis value state output tailMember

/-- A compatible oracle can replay every supported program output. -/
theorem runOracleProgramWithTranscript_replay
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support)
    (compatible : OracleTranscriptCompatible other otherState output.2.2) :
    ∃ finalState, (output.1, finalState, output.2.2) ∈
      (runOracleProgramWithTranscript other program otherState).support := by
  induction program generalizing state otherState output with
  | pure result =>
      simp only [runOracleProgramWithTranscript_pure, PMF.mem_support_map_iff] at member ⊢
      rcases member with ⟨value, valueMember, rfl⟩
      exact ⟨otherState, value, valueMember, rfl⟩
  | query request next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_query, PMF.mem_support_map_iff] at member ⊢
      rcases member with ⟨tailOutput, tailMember, rfl⟩
      obtain ⟨sameAnswer, compatibleTail⟩ := compatible
      obtain ⟨finalState, finalMember⟩ := inductionHypothesis
        (handler request state).1 (handler request state).2
        (other request otherState).2 tailOutput tailMember compatibleTail
      refine ⟨finalState, (tailOutput.1, finalState, tailOutput.2.2), ?_, ?_⟩
      · simpa only [sameAnswer] using finalMember
      · simp only [sameAnswer]
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.mem_support_bind_iff] at member ⊢
      rcases member with ⟨value, valueMember, tailMember⟩
      obtain ⟨finalState, finalMember⟩ :=
        inductionHypothesis value state otherState output tailMember compatible
      exact ⟨finalState, value, valueMember, finalMember⟩

/-- Attainability turns compatibility into an exact support condition. -/
theorem runOracleProgramWithTranscript_support_iff
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (output : Result × State × List (Sigma oracle.Answer))
    (member : output ∈ (runOracleProgramWithTranscript handler program state).support) :
    (∃ finalState, (output.1, finalState, output.2.2) ∈
      (runOracleProgramWithTranscript other program otherState).support) ↔
        OracleTranscriptCompatible other otherState output.2.2 := by
  constructor
  · rintro ⟨finalState, finalMember⟩
    exact runOracleProgramWithTranscript_compatible other program otherState
      (output.1, finalState, output.2.2) finalMember
  · exact runOracleProgramWithTranscript_replay handler other program state otherState output member

/-- Compatible oracles assign equal mass to each public result and transcript. -/
theorem runOracleProgramWithTranscript_mass_eq
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (state : State) (otherState : Other) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (compatible : OracleTranscriptCompatible handler state transcript)
    (otherCompatible : OracleTranscriptCompatible other otherState transcript) :
    ((runOracleProgramWithTranscript handler program state).map
        (fun output => (output.1, output.2.2))) (result, transcript) =
      ((runOracleProgramWithTranscript other program otherState).map
        (fun output => (output.1, output.2.2))) (result, transcript) := by
  classical
  induction program generalizing state otherState transcript with
  | pure distribution =>
      simp only [runOracleProgramWithTranscript_pure, PMF.map_comp, Function.comp_def]
  | query request next inductionHypothesis =>
      cases transcript with
      | nil =>
          simp [runOracleProgramWithTranscript_query, PMF.map_comp, PMF.map_apply]
      | cons entry tail =>
          rcases entry with ⟨query, answer⟩
          by_cases sameQuery : query = request
          · subst query
            obtain ⟨sameAnswer, compatibleTail⟩ := compatible
            obtain ⟨otherAnswer, otherTail⟩ := otherCompatible
            simpa only [runOracleProgramWithTranscript_query, PMF.map_comp, PMF.map_apply,
              Function.comp_apply, Prod.mk.injEq, List.cons.injEq, Sigma.mk.inj_iff,
              sameAnswer, otherAnswer, heq_eq_eq, true_and, and_true] using
              inductionHypothesis answer (handler request state).2
                (other request otherState).2 tail compatibleTail otherTail
          · simp [runOracleProgramWithTranscript_query, PMF.map_comp, PMF.map_apply, sameQuery]
  | sample distribution next inductionHypothesis =>
      simp only [runOracleProgramWithTranscript_sample, PMF.map_bind, PMF.bind_apply]
      apply tsum_congr
      intro value
      rw [inductionHypothesis value state otherState transcript compatible otherCompatible]

/-- An incompatible transcript has zero mass. -/
theorem runOracleProgramWithTranscript_mass_zero
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (result : Result) (transcript : List (Sigma oracle.Answer))
    (incompatible : ¬ OracleTranscriptCompatible handler state transcript) :
    ((runOracleProgramWithTranscript handler program state).map
        (fun output => (output.1, output.2.2))) (result, transcript) = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro member
  rw [PMF.mem_support_map_iff] at member
  obtain ⟨output, outputMember, same⟩ := member
  apply incompatible
  have compatible := runOracleProgramWithTranscript_compatible handler program state output outputMember
  have sameTrace : output.2.2 = transcript := congrArg Prod.snd same
  rwa [sameTrace] at compatible

/-- Oracle sampling separates from the common adversary mass. -/
theorem runOracleProgramWithTranscript_mass_factor
    {oracle : OracleSpec.{uQuery, uAnswer}} {Result : Type uResult}
    {State : Type uState} {Other : Type uOther}
    (handler : OracleHandler oracle State) (reference : OracleHandler oracle Other)
    {budget : Nat} (program : OracleProgram oracle Result budget)
    (states : PMF State) (referenceState : Other) (result : Result)
    (transcript : List (Sigma oracle.Answer))
    (referenceCompatible : OracleTranscriptCompatible reference referenceState transcript) :
    ((states.bind (runOracleProgramWithTranscript handler program)).map
        (fun output => (output.1, output.2.2))) (result, transcript) =
      ((runOracleProgramWithTranscript reference program referenceState).map
        (fun output => (output.1, output.2.2))) (result, transcript) *
          states.toOuterMeasure {state | OracleTranscriptCompatible handler state transcript} := by
  classical
  rw [PMF.map_bind, PMF.bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro state
  by_cases compatible : OracleTranscriptCompatible handler state transcript
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, compatible, if_true]
    rw [runOracleProgramWithTranscript_mass_eq handler reference program
      state referenceState result transcript compatible referenceCompatible, mul_comm]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, compatible, if_false, mul_zero]
    rw [runOracleProgramWithTranscript_mass_zero handler program state result transcript compatible,
      mul_zero]

end Kriterion.ArgoMAC.Security
