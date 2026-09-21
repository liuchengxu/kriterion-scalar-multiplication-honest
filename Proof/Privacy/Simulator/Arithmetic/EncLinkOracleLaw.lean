import Proof.Privacy.Simulator.Arithmetic.EncLinkLazy
import Proof.Privacy.Simulator.StrictOracleLaw

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security Security.OperationalOracle
noncomputable section
set_option maxRecDepth 4096
attribute [local irreducible] encLinkIndices encLinkPrepared lazyEncLinkResult encLinkScheduled lazyEncLinkHashReply

theorem encLinkRows_completion
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (publicCompletion oracle).map (fun complete => (eagerEncLinkRows complete indices suffix memory, complete)) =
      (lazyEncLinkRows indices suffix memory oracle).bind (fun result =>
        (publicCompletion result.2).map (fun complete => (result.1, complete))) := by
  induction indices generalizing memory oracle with
  | nil => simp [eagerEncLinkRows, lazyEncLinkRows]
  | cons index rest ih =>
    let wire := rest.flatMap encLinkIndexBits ++ suffix
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index wire).registers 8).toNat)
    let continuation := fun (answer : Block) (complete : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) =>
      let result := lazyEncLinkResult memory index wire (answerWords request answer)
      if result.2.2 = 7208 then
        let final := eagerEncLinkRows complete rest suffix result.1
        ((final.1, result.2.1 + final.2.1, final.2.2), complete)
      else (result, complete)
    have law := congrArg (PMF.map (fun answer => continuation answer.1 answer.2)) (public_step request oracle)
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at law
    change (publicCompletion oracle).map (fun complete => continuation (publicAnswer complete request) complete) = _ at law
    have left : (publicCompletion oracle).map (fun complete =>
        (eagerEncLinkRows complete (index :: rest) suffix memory, complete)) =
        (publicCompletion oracle).map (fun complete => continuation (publicAnswer complete request) complete) := by
      congr 1
      funext complete
      dsimp only [continuation, eagerEncLinkRows, wire, request]
      split <;> rfl
    rw [left, law]
    simp only [lazyEncLinkRows, PMF.bind_bind]
    apply PMF.bind_congr
    intro answer supported
    dsimp only [continuation]
    split
    · rename_i more
      have tail := congrArg (PMF.map (fun result =>
        ((result.1.1, (lazyEncLinkResult memory index wire (answerWords request answer.1)).2.1 + result.1.2.1,
          result.1.2.2), result.2)))
        (ih (lazyEncLinkResult memory index wire (answerWords request answer.1)).1 answer.2)
      simpa only [PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def, wire, request, more, if_true] using tail
    · rename_i stop
      simp only [wire, request] at stop
      simp only [PMF.pure_bind]
      rfl

/-- Lazy link queries preserve the full eager oracle completion law. -/
theorem encLinkSamples_completion (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (publicCompletion oracle).map (fun complete => (eagerEncLinkSamples complete memory, complete)) =
      (lazyEncLinkSamples memory oracle).bind (fun result =>
        (publicCompletion result.2).map (fun complete => (result.1, complete))) := by
  let saved := executeLinear encLinkSave memory
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
  let ready := fun answer => encLinkScheduled (lazyEncLinkHashReply saved (answerWords request answer))
  have law := congrArg (PMF.map (fun answer : request.Answer × PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex =>
    let result := eagerEncLinkRows answer.2 encLinkIndices (memory.bits 0) (ready answer.1)
    ((result.1, 7139 + result.2.1, result.2.2), answer.2))) (public_step request oracle)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at law
  change (publicCompletion oracle).map (fun complete => (eagerEncLinkSamples complete memory, complete)) = _ at law
  rw [law]
  simp only [lazyEncLinkSamples, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro answer supported
  have rows := congrArg (PMF.map (fun result =>
    ((result.1.1, 7139 + result.1.2.1, result.1.2.2), result.2)))
    (encLinkRows_completion encLinkIndices (memory.bits 0) (ready answer.1) answer.2)
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, ready, saved, request] using rows

/-- Internal link queries preserve the public fixed history. -/
theorem encLinkSamples_history (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (matching : HistoryMatches oracle history)
    (result : (Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (supported : result ∈ (lazyEncLinkSamples memory oracle).support) :
    HistoryMatches result.2 history := by
  have fixed := lazyEncLinkSamples_fixed memory oracle result supported
  simpa only [HistoryMatches, fixed] using matching

/-- Each lazy link result equals one complete-oracle execution. -/
theorem lazyEncLinkSamples_witness (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (result : (Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (supported : result ∈ (lazyEncLinkSamples memory oracle).support) :
    ∃ complete, eagerEncLinkSamples complete memory = result.1 := by
  have law := congrArg (PMF.map Prod.fst) (encLinkSamples_completion memory oracle)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at law
  have const (current : (Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
      (publicCompletion current.2).map (fun _ => current.1) = PMF.pure current.1 := PMF.map_const _ _
  simp_rw [const] at law
  have mapped := PMF.bind_pure_comp Prod.fst (lazyEncLinkSamples memory oracle)
  simp only [Function.comp_def] at mapped
  rw [mapped] at law
  have reached : result.1 ∈ ((lazyEncLinkSamples memory oracle).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  rw [← law] at reached
  obtain ⟨complete, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  exact ⟨complete, same⟩
/-- Link queries and strict gate programs preserve the full adaptive continuation. -/
theorem encLinkSamples_strict_postquery {budget : Nat}
    (memory : Memory) (state : Shared.Simulator.OracleState)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (commands : Memory × Nat × Fin 7468 → List FixedCommand)
    (program : Memory × Nat × Fin 7468 → OracleProgram (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex) Bool budget)
    (matching : HistoryMatches oracle state.fixedTranscript) (initial : state.bad = false) :
    (publicCompletion oracle).bind (fun complete =>
      let result := eagerEncLinkSamples complete memory
      let next := Shared.Simulator.commands
        {state with fixedOracle := complete.1, encOracle := complete.2.1, hashOracle := complete.2.2}
        (commands result)
      if next.bad then PMF.pure false else ((program result).run idealOracleHandler next).map Prod.fst) =
    (lazyEncLinkSamples memory oracle).bind (fun result =>
      match strictCommands result.2 ((commands result.1).map fun command =>
        (Shared.fixedIndex command.1, command.2.1, command.2.2)) with
      | none => PMF.pure false
      | some updated => (LazyOracle.run (program result.1) updated).map Prod.fst) := by
  let follow := fun (result : (Memory × Nat × Fin 7468) × PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) =>
    let next := Shared.Simulator.commands
      {state with fixedOracle := result.2.1, encOracle := result.2.2.1, hashOracle := result.2.2.2}
      (commands result.1)
    if next.bad then PMF.pure false else ((program result.1).run idealOracleHandler next).map Prod.fst
  have law := congrArg (fun distribution => distribution.bind follow) (encLinkSamples_completion memory oracle)
  simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at law
  rw [show (publicCompletion oracle).bind (fun complete => follow (eagerEncLinkSamples complete memory, complete)) = _ from law]
  apply PMF.bind_congr
  intro result supported
  exact sharedCommands_strict_postquery (program result.1) state result.2 (commands result.1)
    (encLinkSamples_history memory oracle state.fixedTranscript matching result supported) initial
end
end Kriterion.ArgoMAC.ArithmeticSimulator
