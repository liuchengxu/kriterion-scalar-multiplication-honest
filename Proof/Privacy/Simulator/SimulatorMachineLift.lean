import Proof.Privacy.Simulator.SimulatorMachineCost
import Proof.Privacy.Simulator.SimulatorCutoff

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling
namespace SimulatorMachine

/-- This compiler marks each internal request in the combined oracle specification. -/
def Program.internal {A : Type} {budget : Nat} : Program spec A budget → Program combinedSpec A budget
  | .pure value => .pure value
  | .query request next => .query (.inl request) (fun answer => (next answer).internal)
  | .map f source => .map f source.internal
  | .bind source next => .bind source.internal (fun answer => (next answer).internal)
  | .weaken source bounded => .weaken source.internal bounded

/-- The compiler preserves every run under the restricted handler. -/
theorem Program.internal_run {A State : Type} {budget : Nat}
    (oracleHandler : OracleHandler combinedSpec State) (program : Program spec A budget)
    (state : State) :
    program.internal.run oracleHandler state =
      program.run (fun request => oracleHandler (.inl request)) state := by
  induction program generalizing state with
  | pure => rfl
  | query request next ih => exact ih _ _
  | map f source ih => simp only [internal, run, ih]
  | bind source next first second => simp only [internal, run, first, second]
  | weaken source bounded ih => exact ih state

/-- The compiler preserves the sparse distribution. -/
theorem Program.internal_sampledLaw {A : Type} {budget : Nat}
    (program : Program spec A budget) (state : SparseState) :
    program.internal.sampledLaw combinedDraw state = program.sampledLaw sparseDraw state := by
  induction program generalizing state with
  | pure => rfl
  | query request next ih =>
    simp only [internal, sampledLaw, combinedDraw, ih]
  | map f source ih => simp only [internal, sampledLaw, ih]
  | bind source next first second => simp only [internal, sampledLaw, first, second]
  | weaken source bounded ih => exact ih state

/-- The compiler preserves the executable finite retry program. -/
theorem Program.internal_cutoff {A : Type} {budget : Nat}
    (program : Program spec A budget) (attempts : Nat) (state : SparseState) :
    program.internal.cutoff combinedDraw attempts state = program.cutoff sparseDraw attempts state := by
  induction program generalizing state with
  | pure => rfl
  | query request next ih =>
    simp only [internal, cutoff, combinedDraw]
    congr 1
    funext answer
    cases answer with
    | none => rfl
    | some answer => exact ih _ _
  | map f source ih => simp only [internal, cutoff, ih]
  | bind source next first second =>
    simp only [internal, cutoff, first]
    congr 1
    funext answer
    cases answer with
    | none => rfl
    | some answer => exact second _ _
  | weaken source bounded ih => exact ih state

private theorem drawSizeLe_of_bound {A : Type} (draw : Draw A) (maximum : Nat)
    (bounded : Cost.drawBound draw ≤ maximum) : drawSizeLe maximum draw := by
  cases draw with
  | pure => trivial
  | uniform => exact bounded

/-- Every internal draw satisfies the finite bit sampler's range premise. -/
theorem sparseDraw_sizeLe (request : spec.Query) (state : SparseState) :
    drawSizeLe (2 ^ 256) (sparseDraw request state) :=
  drawSizeLe_of_bound _ _ (Cost.sparseDraw_bound request state)

/-- Every combined draw satisfies the finite bit sampler's range premise. -/
theorem combinedDraw_sizeLe (request : combinedSpec.Query) (state : SparseState) :
    drawSizeLe (2 ^ 256) (combinedDraw request state) :=
  drawSizeLe_of_bound _ _ (Cost.combinedDraw_bound request state)

/-- The internal finite program has a strict fair-bit bound. -/
theorem Program.sparse_cutoff_bits {A Seed : Type} {budget : Nat}
    (program : Program spec A budget)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (state : SparseState) (seed : Seed) :
    ((program.cutoff sparseDraw attempts state).run random seed).2 ≤ budget * (257 * attempts) :=
  program.cutoff_bit_bound sparseDraw sparseDraw_sizeLe random attempts state seed

/-- The combined finite program has a strict fair-bit bound. -/
theorem Program.combined_cutoff_bits {A Seed : Type} {budget : Nat}
    (program : Program combinedSpec A budget)
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (state : SparseState) (seed : Seed) :
    ((program.cutoff combinedDraw attempts state).run random seed).2 ≤ budget * (257 * attempts) :=
  program.cutoff_bit_bound combinedDraw combinedDraw_sizeLe random attempts state seed

end SimulatorMachine
end Kriterion.ArgoMAC.Security
