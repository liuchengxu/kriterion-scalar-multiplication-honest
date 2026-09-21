import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The response parser charges the query and retains only a complete answer. -/
def parsedResponse [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine)
    (request : PublicQuery FixedIndex EncIndex) (state : State) :
    PMF (Option (request.Answer × State)) :=
  bindCutoff (respond machine ([true, false] ++ GarbledCircuit.SimulatorProtocol.query request)
    {state with queries := state.queries + 1}) fun result =>
      PMF.pure ((answer request result.1).map fun value => (value, result.2))

/-- The option transformer retains the same cutoff branches. -/
theorem optionT_run_bind_cutoff {A B : Type} (distribution : OptionT PMF A)
    (next : A → OptionT PMF B) :
    (distribution >>= next).run = bindCutoff distribution.run (fun value => (next value).run) := by
  rw [OptionT.run_bind]
  unfold Option.elimM bindCutoff
  congr 1
  funext result
  cases result <;> rfl

/-- The protocol program uses exactly the parsed response handler. -/
theorem runProgram_parsed [BN254.FieldCertificate] {FixedIndex EncIndex Result : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine) {budget : Nat}
    (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget) (state : State) :
    (runProgram machine program state).run = runSampledCutoff (parsedResponse machine) program state := by
  induction program generalizing state with
  | pure distribution =>
      rw [runProgram, optionT_run_bind_cutoff]
      change bindCutoff (distribution.bind (fun value => PMF.pure (some value)))
        (fun value => PMF.pure (some (value, state))) = _
      simp only [bindCutoff, PMF.bind_bind, PMF.pure_bind, runSampledCutoff]
      rfl
  | sample distribution next ih =>
      rw [runProgram, optionT_run_bind_cutoff]
      change bindCutoff (distribution.bind (fun value => PMF.pure (some value)))
        (fun value => (runProgram machine (next value) state).run) = _
      simp only [bindCutoff, PMF.bind_bind, PMF.pure_bind, runSampledCutoff, ih]
  | query request next ih =>
      rw [runProgram, optionT_run_bind_cutoff]
      simp only [optionT_run_bind_cutoff, OptionT.run_mk, runSampledCutoff,
        parsedResponse, bindCutoff, PMF.bind_bind]
      congr 1
      funext result
      cases result with
      | none => simp only [PMF.pure_bind]
      | some result =>
          simp only [PMF.pure_bind]
          cases answer request result.1 <;> simp_all

/-- Each accepted program result preserves the response invariant. -/
theorem runSampledCutoff_ready {oracle : OracleSpec} {Result State : Type}
    (handler : ∀ request, State → PMF (Option (oracle.Answer request × State)))
    (ready : State → Prop)
    (preserved : ∀ request state, ready state → ∀ value next,
      some (value, next) ∈ (handler request state).support → ready next)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (initial : ready state) (value : Result) (final : State)
    (member : some (value, final) ∈ (runSampledCutoff handler program state).support) : ready final := by
  induction program generalizing state with
  | pure distribution =>
      obtain ⟨result, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      cases same
      exact initial
  | sample distribution next ih =>
      obtain ⟨sample, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih sample state initial member
  | query request next ih =>
      obtain ⟨result, accepted, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      cases result with
      | none => simpa using member
      | some result =>
          exact ih result.1 result.2 (preserved request state initial result.1 result.2 accepted) member

/-- The state decoder commutes with every supported adaptive continuation. -/
theorem runSampledCutoff_decode {oracle : OracleSpec} {Result State Source : Type}
    (handler : ∀ request, State → PMF (Option (oracle.Answer request × State)))
    (source : ∀ request, Source → PMF (Option (oracle.Answer request × Source)))
    (decode : State → Source) (ready : State → Prop)
    (same : ∀ request state, ready state →
      (handler request state).map (Option.map fun result => (result.1, decode result.2)) =
        source request (decode state))
    (preserved : ∀ request state, ready state → ∀ value next,
      some (value, next) ∈ (handler request state).support → ready next)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (initial : ready state) :
    (runSampledCutoff handler program state).map (Option.map fun result => (result.1, decode result.2)) =
      runSampledCutoff source program (decode state) := by
  induction program generalizing state with
  | pure distribution => simp only [runSampledCutoff, PMF.map_comp]; rfl
  | sample distribution next ih =>
      simp only [runSampledCutoff, PMF.map_bind]
      congr 1
      funext value
      exact ih value state initial
  | query request next ih =>
      simp only [runSampledCutoff, bindCutoff, PMF.map_bind]
      rw [← same request state initial, PMF.bind_map]
      apply PMF.bind_congr
      intro result member
      cases result with
      | none => simp only [Function.comp_apply, Option.map_none, PMF.pure_map]
      | some result =>
          exact ih result.1 result.2 (preserved request state initial result.1 result.2 member)

/-- The complete protocol has the same decoded source distribution. -/
theorem runProgram_source [BN254.FieldCertificate] {FixedIndex EncIndex Result Source : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine)
    (source : ∀ request : PublicQuery FixedIndex EncIndex, Source → PMF (Option (request.Answer × Source)))
    (decode : State → Source) (ready : State → Prop)
    (same : ∀ request state, ready state →
      (parsedResponse machine request state).map (Option.map fun result => (result.1, decode result.2)) =
        source request (decode state))
    (preserved : ∀ (request : PublicQuery FixedIndex EncIndex) state, ready state → ∀ value next,
      some (value, next) ∈ (parsedResponse machine request state).support → ready next)
    {budget : Nat} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : State) (initial : ready state) :
    (runProgram machine program state).run.map (Option.map fun result => (result.1, decode result.2)) =
      runSampledCutoff source program (decode state) := by
  rw [runProgram_parsed]
  exact runSampledCutoff_decode _ source decode ready same preserved program state initial

/-- The complete protocol preserves the response invariant. -/
theorem runProgram_ready [BN254.FieldCertificate] {FixedIndex EncIndex Result : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine) (ready : State → Prop)
    (preserved : ∀ (request : PublicQuery FixedIndex EncIndex) state, ready state → ∀ value next,
      some (value, next) ∈ (parsedResponse machine request state).support → ready next)
    {budget : Nat} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : State) (initial : ready state) (value : Result) (final : State)
    (member : some (value, final) ∈ (runProgram machine program state).run.support) : ready final := by
  rw [runProgram_parsed] at member
  exact runSampledCutoff_ready _ ready preserved program state initial value final member

/-- One joint program retains both exact marginals and the state relation. -/
theorem runProgram_coupling [BN254.FieldCertificate] {FixedIndex EncIndex Result Source : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine)
    (source : ∀ request : PublicQuery FixedIndex EncIndex, Source → PMF (Option (request.Answer × Source)))
    (joint : ∀ request : PublicQuery FixedIndex EncIndex,
      (State × Source) → PMF (Option (request.Answer × (State × Source))))
    (related : State → Source → Prop)
    (left : ∀ request state, related state.1 state.2 →
      (joint request state).map (Option.map fun result => (result.1, result.2.1)) =
        parsedResponse machine request state.1)
    (right : ∀ request state, related state.1 state.2 →
      (joint request state).map (Option.map fun result => (result.1, result.2.2)) =
        source request state.2)
    (preserved : ∀ request state, related state.1 state.2 → ∀ value next,
      some (value, next) ∈ (joint request state).support → related next.1 next.2)
    {budget : Nat} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (state : State) (initialSource : Source) (initial : related state initialSource) :
    let law := runSampledCutoff joint program (state, initialSource)
    law.map (Option.map fun result => (result.1, result.2.1)) = (runProgram machine program state).run ∧
    law.map (Option.map fun result => (result.1, result.2.2)) = runSampledCutoff source program initialSource ∧
    ∀ value final, some (value, final) ∈ law.support → related final.1 final.2 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [runProgram_parsed]
    exact runSampledCutoff_decode joint (parsedResponse machine) Prod.fst
      (fun pair => related pair.1 pair.2) left preserved program (state, initialSource) initial
  · exact runSampledCutoff_decode joint source Prod.snd
      (fun pair => related pair.1 pair.2) right preserved program (state, initialSource) initial
  · intro value final member
    exact runSampledCutoff_ready joint (fun pair => related pair.1 pair.2)
      preserved program (state, initialSource) initial value final member

end
end Kriterion.ArgoMAC.ArithmeticSimulator
