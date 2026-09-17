import Proof.Privacy.Simulator.OperationalOracleLaw

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography
noncomputable section

/-- A request reads or programs one permutation. -/
inductive ProgramAction (size : Nat) where
  | forward (input : Fin size)
  | inverse (output : Fin size)
  | program (input target : Fin size)

/-- Programming returns the target value after it updates the oracle. -/
abbrev programSpec (size : Nat) : OracleSpec where
  Query := ProgramAction size
  Answer := fun _ => Fin size

/-- The eager interpreter keeps the base permutation and its exact deferred swaps. -/
def programEager {size : Nat} :
    OracleHandler (programSpec size) (ProgrammedPermutation size × Equiv.Perm (Fin size))
  | .forward input, (state, π) =>
      (state.denote π input, { state with base := state.base.afterForward input (π input) }, π)
  | .inverse output, (state, π) =>
      let target := (swaps state.overlay).symm output
      (π.symm target, { state with base := state.base.afterInverse target (π.symm target) }, π)
  | .program input target, (state, π) =>
      (target, state.afterProgram target (π input) (state.base.afterForward input (π input)), π)

/-- The sparse interpreter never samples a full permutation. -/
def programSampled {size : Nat} :
    ∀ request : (programSpec size).Query,
      ProgrammedPermutation size → PMF ((programSpec size).Answer request × ProgrammedPermutation size)
  | .forward input, state => (state.forward input).distribution
  | .inverse output, state => (state.inverse output).distribution
  | .program input target, state => (state.program input target).distribution.map (fun next => (target, next))

/-- The completion kernel retains all correlations in the stored base pairs. -/
def programCompletion {size : Nat} (state : ProgrammedPermutation size) :
    PMF (ProgrammedPermutation size × Equiv.Perm (Fin size)) :=
  (PMF.uniformOfFintype state.base.Completion).map (fun π => (state, π.val))

/-- Every query and programming request preserves the complete joint oracle law. -/
theorem program_step {size : Nat} (request : (programSpec size).Query)
    (state : ProgrammedPermutation size) :
    (programCompletion state).map (programEager request) =
      (programSampled request state).bind (fun answer =>
        (programCompletion answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  cases request with
  | forward input =>
      have law := congrArg
        (fun distribution : PMF (Fin size × SparsePermutation size × Equiv.Perm (Fin size)) =>
          distribution.map (fun output =>
            (swaps state.overlay output.1, { state with base := output.2.1 }, output.2.2)))
        (state.base.forward_joint input)
      simpa only [programCompletion, programEager, programSampled, ProgrammedPermutation.forward,
        ProgrammedPermutation.denote, Draw.map_distribution, PMF.map_comp, PMF.map_bind,
        PMF.bind_map, Function.comp_def, Equiv.trans_apply] using law
  | inverse output =>
      have law := congrArg
        (fun distribution : PMF (Fin size × SparsePermutation size × Equiv.Perm (Fin size)) =>
          distribution.map (fun result =>
            (result.1, { state with base := result.2.1 }, result.2.2)))
        (state.base.inverse_joint ((swaps state.overlay).symm output))
      simpa only [programCompletion, programEager, programSampled, ProgrammedPermutation.inverse,
        Draw.map_distribution, PMF.map_comp, PMF.map_bind, PMF.bind_map, Function.comp_def] using law
  | program input target =>
      have law := congrArg
        (fun distribution : PMF (Fin size × SparsePermutation size × Equiv.Perm (Fin size)) =>
          distribution.map (fun output =>
            (target, state.afterProgram target output.1 output.2.1, output.2.2)))
        (state.base.forward_joint input)
      simpa only [programCompletion, programEager, programSampled, ProgrammedPermutation.program,
        ProgrammedPermutation.afterProgram, Draw.map_distribution, PMF.map_comp, PMF.map_bind,
        PMF.bind_map, Function.comp_def] using law


end
end Kriterion.ArgoMAC.Security.OperationalOracle
