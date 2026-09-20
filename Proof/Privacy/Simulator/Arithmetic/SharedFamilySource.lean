import Proof.Privacy.Simulator.Arithmetic.SharedFamilyReindex

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The physical shared source retains its finite tables and its transcript metadata. -/
structure SharedOracleSource where
  family : SparseOracleFamily
  metadata : Metadata

/-- The named source and physical source carry exactly the same finite data. -/
def sharedSourceEquiv : SharedOracleSource ≃ SparseState where
  toFun state := ⟨namedOracleData state.family, state.metadata⟩
  invFun state := ⟨namedOracleDataEquiv.symm state.oracles, state.metadata⟩
  left_inv state := by
    change SharedOracleSource.mk (namedOracleDataEquiv.symm (namedOracleDataEquiv state.family)) state.metadata = state
    rw [namedOracleDataEquiv.symm_apply_apply]
  right_inv state := by
    change SparseState.mk (namedOracleDataEquiv (namedOracleDataEquiv.symm state.oracles)) state.metadata = state
    rw [namedOracleDataEquiv.apply_symm_apply]

/-- The completion kernel attaches the exact shared eager oracle to physical source data. -/
def sharedSourceCompletion (state : SharedOracleSource) : PMF SharedState := completion (sharedSourceEquiv state)

/-- The source interpreter uses the actual physical family for each internal operation. -/
def sharedInternalSourceDraw (request : spec.Query) (state : SharedOracleSource) :
    Draw (spec.Answer request × SharedOracleSource) :=
  match request with
  | .read query =>
      (oracleFamilyDraw (physicalRequest (lowerRequest (.read query))) state.family).map
        (fun result => (lowerAnswer (.read query) (namedAnswer (lowerRequest (.read query)) result.1),
          {state with family := result.2}))
  | .program command =>
      if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 then
        (oracleFamilyDraw (physicalRequest (lowerRequest (.program command))) state.family).map
          (fun result => ((), ⟨result.2, state.metadata.program command⟩))
      else .pure ((), {state with metadata := state.metadata.markBad})

private theorem draw_map_map {A B C : Type} (draw : Draw A) (first : A → B) (second : B → C) :
    (draw.map first).map second = draw.map (fun value => second (first value)) := by cases draw <;> rfl

/-- The internal physical source preserves the named shared source exactly. -/
theorem sharedInternalSourceDraw_named (request : spec.Query) (state : SharedOracleSource) :
    (sharedInternalSourceDraw request state).map (fun result => (result.1, sharedSourceEquiv result.2)) =
      sparseDraw request (sharedSourceEquiv state) := by
  cases request with
  | read query =>
      have law := congrArg (Draw.map (fun result =>
        (lowerAnswer (.read query) result.1, (⟨result.2, state.metadata⟩ : SparseState))))
        (oracleFamilyDraw_named (lowerRequest (.read query)) state.family)
      simpa only [sharedInternalSourceDraw, sparseDraw, sharedSourceEquiv, Equiv.coe_fn_mk, draw_map_map] using law
  | program command =>
      change (sharedInternalSourceDraw (.program command) state).map _ =
        if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 then
          (lowerDraw (lowerRequest (.program command)) (namedOracleData state.family)).map
            (fun result => ((), (⟨result.2, state.metadata.program command⟩ : SparseState)))
        else .pure ((), ⟨namedOracleData state.family, state.metadata.markBad⟩)
      by_cases fresh : freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 = true
      · have law := congrArg (Draw.map (fun result =>
          ((), (⟨result.2, state.metadata.program command⟩ : SparseState))))
          (oracleFamilyDraw_named (lowerRequest (.program command)) state.family)
        simp only [sharedInternalSourceDraw, if_pos fresh, draw_map_map] at law ⊢
        exact law
      · simp only [sharedInternalSourceDraw, if_neg fresh, Draw.map]
        rfl

/-- The external source records its visible public reply after the physical oracle step. -/
def sharedExternalSourceDraw (query : SharedQuery) (state : SharedOracleSource) :
    Draw (SharedAnswer query × SharedOracleSource) :=
  (sharedInternalSourceDraw (.read query) state).map (fun result =>
    (result.1, {result.2 with metadata := result.2.metadata.record query result.1}))

/-- The combined physical source shares one family across internal and public requests. -/
def sharedCombinedSourceDraw (query : combinedSpec.Query) (state : SharedOracleSource) :
    Draw (combinedSpec.Answer query × SharedOracleSource) :=
  match query with
  | .inl request => sharedInternalSourceDraw request state
  | .inr query => sharedExternalSourceDraw query state

/-- The combined physical source has the exact named law with all transcript metadata. -/
theorem sharedCombinedSourceDraw_named (query : combinedSpec.Query) (state : SharedOracleSource) :
    (sharedCombinedSourceDraw query state).map (fun result => (result.1, sharedSourceEquiv result.2)) =
      combinedDraw query (sharedSourceEquiv state) := by
  cases query with
  | inl request => exact sharedInternalSourceDraw_named request state
  | inr query =>
      have law := congrArg (Draw.map (fun result : SharedAnswer query × SparseState =>
        (result.1, {result.2 with metadata := result.2.metadata.record query result.1})))
        (sharedInternalSourceDraw_named (.read query) state)
      simpa only [sharedCombinedSourceDraw, sharedExternalSourceDraw, combinedDraw, externalDraw,
        draw_map_map, sharedSourceEquiv, Equiv.coe_fn_mk] using law

/-- The physical source law never samples a complete random oracle. -/
def sharedCombinedSourceHandler (query : combinedSpec.Query) (state : SharedOracleSource) :
    PMF (combinedSpec.Answer query × SharedOracleSource) := (sharedCombinedSourceDraw query state).distribution

/-- Every physical source step preserves the actual shared eager simulator law. -/
theorem sharedCombinedSource_step (query : combinedSpec.Query) (state : SharedOracleSource) :
    (sharedSourceCompletion state).map (combinedEager query) =
      (sharedCombinedSourceHandler query state).bind (fun result =>
        (sharedSourceCompletion result.2).map (fun eager => (result.1, eager))) := by
  have named := congrArg Draw.distribution (sharedCombinedSourceDraw_named query state)
  rw [Draw.map_distribution] at named
  have step := combined_step query (sharedSourceEquiv state)
  rw [combinedHandler, ← named] at step
  simpa only [sharedSourceCompletion, sharedCombinedSourceHandler, PMF.bind_map, Function.comp_def] using step

/-- Every adaptive interleaving preserves the actual shared simulator's complete conditional law. -/
theorem sharedCombinedSource_adaptive_joint {Result : Type} {budget : Nat}
    (program : OracleProgram combinedSpec Result budget) (state : SharedOracleSource) :
    (sharedSourceCompletion state).bind (fun eager => program.run combinedEager eager) =
      (runSampled sharedCombinedSourceHandler program state).bind (fun result =>
        (sharedSourceCompletion result.2).map (fun eager => (result.1, eager))) :=
  adaptive_joint_law combinedEager sharedCombinedSourceHandler sharedSourceCompletion sharedCombinedSource_step program state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
