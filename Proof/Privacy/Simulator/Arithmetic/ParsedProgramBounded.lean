import Proof.Privacy.Simulator.Arithmetic.ParsedProgramSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- Each accepted program result retains a relation at its actual query count. -/
theorem runSampledCutoff_boundedReady {oracle : OracleSpec} {Result State : Type}
    (handler : ∀ request, State → PMF (Option (oracle.Answer request × State)))
    (total : Nat) (ready : Nat → State → Prop)
    (preserved : ∀ used request state, used < total → ready used state → ∀ value next,
      some (value, next) ∈ (handler request state).support → ready (used + 1) next)
    {budget : Nat} (program : OracleProgram oracle Result budget) (used : Nat) (state : State)
    (room : used + budget ≤ total) (initial : ready used state) (value : Result) (final : State)
    (member : some (value, final) ∈ (runSampledCutoff handler program state).support) :
    ∃ finalUsed, used ≤ finalUsed ∧ finalUsed ≤ used + budget ∧ ready finalUsed final := by
  induction program generalizing used state with
  | pure distribution =>
      obtain ⟨result, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      cases same
      exact ⟨used, le_rfl, Nat.le_add_right _ _, initial⟩
  | sample distribution next ih =>
      obtain ⟨sample, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      exact ih sample used state room initial member
  | query request next ih =>
      obtain ⟨result, accepted, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
      cases result with
      | none => simpa using member
      | some result =>
          obtain ⟨finalUsed, lower, upper, related⟩ := ih result.1 (used + 1) result.2
            (by omega) (preserved used request state (by omega) initial result.1 result.2 accepted) member
          exact ⟨finalUsed, by omega, by omega, related⟩

/-- The decoder needs a query law only while the program has query capacity. -/
theorem runSampledCutoff_boundedDecode {oracle : OracleSpec} {Result State Source : Type}
    (handler : ∀ request, State → PMF (Option (oracle.Answer request × State)))
    (source : ∀ request, Source → PMF (Option (oracle.Answer request × Source)))
    (decode : State → Source) (total : Nat) (ready : Nat → State → Prop)
    (same : ∀ used request state, used < total → ready used state →
      (handler request state).map (Option.map fun result => (result.1, decode result.2)) =
        source request (decode state))
    (preserved : ∀ used request state, used < total → ready used state → ∀ value next,
      some (value, next) ∈ (handler request state).support → ready (used + 1) next)
    {budget : Nat} (program : OracleProgram oracle Result budget) (used : Nat) (state : State)
    (room : used + budget ≤ total) (initial : ready used state) :
    (runSampledCutoff handler program state).map (Option.map fun result => (result.1, decode result.2)) =
      runSampledCutoff source program (decode state) := by
  induction program generalizing used state with
  | pure distribution => simp only [runSampledCutoff, PMF.map_comp]; rfl
  | sample distribution next ih =>
      simp only [runSampledCutoff, PMF.map_bind]
      congr 1
      funext value
      exact ih value used state room initial
  | query request next ih =>
      simp only [runSampledCutoff, bindCutoff, PMF.map_bind]
      rw [← same used request state (by omega) initial, PMF.bind_map]
      apply PMF.bind_congr
      intro result member
      cases result with
      | none => simp only [Function.comp_apply, Option.map_none, PMF.pure_map]
      | some result =>
          exact ih result.1 (used + 1) result.2 (by omega)
            (preserved used request state (by omega) initial result.1 result.2 member)

/-- The bounded joint program retains both marginals and its final query count. -/
theorem runProgram_boundedCoupling [BN254.FieldCertificate] {FixedIndex EncIndex Result Source : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Machine)
    (source : ∀ request : PublicQuery FixedIndex EncIndex, Source → PMF (Option (request.Answer × Source)))
    (joint : ∀ request : PublicQuery FixedIndex EncIndex,
      (State × Source) → PMF (Option (request.Answer × (State × Source))))
    (total : Nat) (related : Nat → State → Source → Prop)
    (left : ∀ used request state, used < total → related used state.1 state.2 →
      (joint request state).map (Option.map fun result => (result.1, result.2.1)) =
        parsedResponse machine request state.1)
    (right : ∀ used request state, used < total → related used state.1 state.2 →
      (joint request state).map (Option.map fun result => (result.1, result.2.2)) =
        source request state.2)
    (preserved : ∀ used request state, used < total → related used state.1 state.2 → ∀ value next,
      some (value, next) ∈ (joint request state).support → related (used + 1) next.1 next.2)
    {budget : Nat} (program : OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget)
    (used : Nat) (state : State) (initialSource : Source) (room : used + budget ≤ total)
    (initial : related used state initialSource) :
    let law := runSampledCutoff joint program (state, initialSource)
    law.map (Option.map fun result => (result.1, result.2.1)) = (runProgram machine program state).run ∧
    law.map (Option.map fun result => (result.1, result.2.2)) = runSampledCutoff source program initialSource ∧
    ∀ value final, some (value, final) ∈ law.support →
      ∃ finalUsed, used ≤ finalUsed ∧ finalUsed ≤ used + budget ∧ related finalUsed final.1 final.2 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [runProgram_parsed]
    exact runSampledCutoff_boundedDecode joint (parsedResponse machine) Prod.fst total
      (fun used pair => related used pair.1 pair.2) left preserved program used (state, initialSource) room initial
  · exact runSampledCutoff_boundedDecode joint source Prod.snd total
      (fun used pair => related used pair.1 pair.2) right preserved program used (state, initialSource) room initial
  · intro value final member
    exact runSampledCutoff_boundedReady joint total (fun used pair => related used pair.1 pair.2)
      preserved program used (state, initialSource) room initial value final member

end
end Kriterion.ArgoMAC.ArithmeticSimulator
