import Proof.Privacy.Simulator.SimulatorRejectionCost
import Proof.Privacy.Simulator.SimulatorTotalLaw
import Proof.Privacy.Simulator.SimulatorMachineCost

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle BoundedIntegerSampling SimulatorSampling SimulatorMachine

namespace BoundedIntegerSampling

/-- This sampler returns zero when every bounded rejection attempt fails. -/
def totalInteger (size : Nat) (positive : 0 < size) (attempts : Nat) : BitCode (Fin size) :=
  (cutoff size attempts).bind fun value => .pure (value.getD ⟨0, positive⟩)

theorem totalInteger_bits {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (size : Nat) (positive : 0 < size) (attempts : Nat)
    (bounded : size ≤ 2 ^ 256) (seed : Seed) :
    ((totalInteger size positive attempts).run random seed).2 ≤ 257 * attempts := by
  simpa only [totalInteger, BitCode.bind_run, BitCode.run, Nat.add_zero] using
    cutoff_run_bits_le_257 random size positive bounded attempts seed

theorem totalInteger_positive (size : Nat) (positive : 0 < size) (attempts : Nat) :
    SimulatorRejectionCost.PositiveWidths (totalInteger size positive attempts) :=
  SimulatorRejectionCost.positive_bind _ _ (SimulatorRejectionCost.cutoff_positive _ _) (fun _ => trivial)


/-- The fallback preserves the mass of every accepted integer. -/
theorem totalInteger_dominates (size : Nat) (positive : 0 < size) (attempts : Nat) (value : Fin size) :
    (cutoff size attempts).law (some value) ≤ (totalInteger size positive attempts).law value := by
  rw [totalInteger, BitCode.bind_law, PMF.bind_apply]
  have term := ENNReal.le_tsum (f := fun item : Option (Fin size) =>
    (cutoff size attempts).law item * (BitCode.pure (item.getD ⟨0, positive⟩)).law value) (some value)
  simpa only [Option.getD_some, BitCode.law, PMF.pure_apply_self, mul_one] using term

theorem totalInteger_law (size : Nat) (positive : 0 < size) (attempts : Nat) :
    TotalLaw attempts 1 (Code.draw size positive).law (totalInteger size positive attempts).law :=
  (CutoffLaw.code attempts (Code.draw size positive)).total (totalInteger_dominates size positive attempts)

/-- The bounded-integer callback uses the same finite fair-bit sampler. -/
def totalRandom {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (size : Nat) (positive : 0 < size) (seed : Seed) : Fin size × Seed :=
  ((totalInteger size positive attempts).run random seed).1

/-- This source records every supplied bit in its state. -/
def countedSource {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (width : Nat) (state : Seed × Nat) : Fin (2 ^ width) × (Seed × Nat) :=
  let sampled := random width state.1
  (sampled.1, sampled.2, state.2 + width)

theorem run_countedSource {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (seed : Seed) (used : Nat) :
    (code.run (countedSource random) (seed, used)) =
      (((code.run random seed).1.1, (code.run random seed).1.2,
        used + (code.run random seed).2), (code.run random seed).2) := by
  induction code generalizing seed used with
  | pure => simp [BitCode.run]
  | bits width next ih => simp only [BitCode.run, countedSource, ih, Nat.add_assoc]

end BoundedIntegerSampling
namespace SimulatorSampling

/-- This private sampler always returns a value and continues after a fallback draw. -/
def Code.total {A : Type} {count : Nat} (attempts : Nat) : Code A count → BitCode A
  | .pure value => .pure value
  | .draw size positive => totalInteger size positive attempts
  | .bind source next => (source.total attempts).bind fun value => (next value).total attempts


/-- Total private sampling retains the required common output mass. -/
theorem Code.total_law {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    TotalLaw attempts count code.law (code.total attempts).law := by
  induction code with
  | pure value => exact TotalLaw.exact attempts (PMF.pure value)
  | draw size positive => exact totalInteger_law size positive attempts
  | bind source next first second =>
      simpa only [Code.law, Code.total, BitCode.bind_law] using first.bind second

/-- The total private sampler executes the same bounded-integer program. -/
theorem Code.total_run {A Seed : Type} {count : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (code : Code A count) (seed : Seed) :
    ((code.total attempts).run random seed).1 = code.run (totalRandom random attempts) seed := by
  induction code generalizing seed with
  | pure => rfl
  | draw => rfl
  | bind source next first second =>
      simp only [Code.total, BitCode.bind_run, Code.run, second, first]

theorem Code.total_positive {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    SimulatorRejectionCost.PositiveWidths (code.total attempts) := by
  induction code with
  | pure => trivial
  | draw size positive => exact totalInteger_positive size positive attempts
  | bind source next first second => exact SimulatorRejectionCost.positive_bind _ _ first second

/-- The private sampler has a strict bit bound even when it uses fallback values. -/
theorem Code.total_bits {A Seed : Type} {count : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (code : Code A count) (bounded : code.DrawSizeLe (2 ^ 256)) (seed : Seed) :
    ((code.total attempts).run random seed).2 ≤ count * (257 * attempts) := by
  induction code generalizing seed with
  | pure => simp [Code.total, BitCode.run]
  | draw size positive => simpa only [Code.total, Nat.one_mul] using totalInteger_bits random size positive attempts bounded seed
  | bind source next first second =>
      simp only [Code.total, BitCode.bind_run, Nat.add_mul]
      exact Nat.add_le_add (first bounded.1 seed) (second _ (bounded.2 _) _)

end SimulatorSampling
namespace SimulatorMachine

/-- Each total sparse draw returns a supported integer result after finite sampling. -/
def totalDraw {A : Type} (attempts : Nat) : Draw A → BitCode A
  | .pure value => .pure value
  | .uniform size positive next => (totalInteger size positive attempts).bind fun value => .pure (next value)


/-- A total sparse draw retains the exact draw's common mass. -/
theorem totalDraw_law {A : Type} (attempts : Nat) (draw : Draw A) :
    TotalLaw attempts 1 draw.distribution (totalDraw attempts draw).law := by
  cases draw with
  | pure value => exact (TotalLaw.exact attempts (PMF.pure value)).weaken (by decide : 0 ≤ 1)
  | uniform size positive next =>
      simpa only [Draw.distribution, totalDraw, BitCode.bind_law, BitCode.law, Code.law, PMF.map, Function.comp_def] using
        (totalInteger_law size positive attempts).map next

theorem totalDraw_run {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (draw : Draw A) (seed : Seed) :
    ((totalDraw attempts draw).run random seed).1 = runDraw (totalRandom random attempts) draw seed := by
  cases draw <;> simp only [totalDraw, BitCode.bind_run, BitCode.run, runDraw, totalRandom]

theorem totalDraw_positive {A : Type} (attempts : Nat) (draw : Draw A) :
    SimulatorRejectionCost.PositiveWidths (totalDraw attempts draw) := by
  cases draw with
  | pure => trivial
  | uniform size positive next =>
      exact SimulatorRejectionCost.positive_bind _ _ (totalInteger_positive size positive attempts) (fun _ => trivial)

theorem totalDraw_bits {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (draw : Draw A) (bounded : drawSizeLe (2 ^ 256) draw) (seed : Seed) :
    ((totalDraw attempts draw).run random seed).2 ≤ 257 * attempts := by
  cases draw with
  | pure => simp [totalDraw, BitCode.run]
  | uniform size positive next =>
      simpa only [totalDraw, BitCode.bind_run, BitCode.run, Nat.add_zero] using
        totalInteger_bits random size positive attempts bounded seed

/-- The total oracle program continues after every finite fallback draw. -/
def Program.total {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) : Program oracle A budget → State → BitCode (A × State)
  | .pure value, state => .pure (value, state)
  | .query request next, state => (totalDraw attempts (sparse request state)).bind
      fun answer => (next answer.1).total sparse attempts answer.2
  | .map f source, state => (source.total sparse attempts state).bind
      fun answer => .pure (f answer.1, answer.2)
  | .bind source next, state => (source.total sparse attempts state).bind
      fun answer => (next answer.1).total sparse attempts answer.2
  | .weaken source _, state => source.total sparse attempts state


/-- Total finite execution retains common mass with the exact oracle program. -/
theorem Program.total_law {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) :
    TotalLaw attempts budget (program.sampledLaw sparse state) (program.total sparse attempts state).law := by
  induction program generalizing state with
  | pure value => exact TotalLaw.exact attempts (PMF.pure (value, state))
  | query request next ih =>
      simpa only [Program.sampledLaw, Program.total, BitCode.bind_law, Nat.add_comm] using
        (totalDraw_law attempts (sparse request state)).bind (fun answer => ih answer.1 answer.2)
  | map f source ih =>
      simpa only [Program.sampledLaw, Program.total, BitCode.bind_law, BitCode.law, PMF.map, Function.comp_def] using
        (ih state).map (fun answer => (f answer.1, answer.2))
  | bind source next first second =>
      simpa only [Program.sampledLaw, Program.total, BitCode.bind_law] using
        (first state).bind (fun answer => second answer.1 answer.2)
  | weaken source bounded ih => exact (ih state).weaken bounded

/-- The complete integer interpreter has the total finite program's value and seed. -/
theorem Program.total_run {oracle : OracleSpec.{0, 0}} {A State Seed : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (program : Program oracle A budget) (state : State) (seed : Seed) :
    let result := (program.total sparse attempts state).run random seed
    (result.1.1.1, result.1.1.2, result.1.2) =
      program.execute sparse (totalRandom random attempts) state seed := by
  induction program generalizing state seed with
  | pure => rfl
  | query request next ih =>
      simp only [Program.total, BitCode.bind_run]
      rw [ih]
      simp only [totalDraw_run]
      rfl
  | map f source ih =>
      simp only [Program.total, BitCode.bind_run, BitCode.run, Program.execute, Program.run]
      have same := ih state seed
      simp only [Program.execute] at same
      rw [← same]
  | bind source next first second =>
      simp only [Program.total, BitCode.bind_run]
      rw [second]
      have same := first state seed
      simp only [Program.execute, Program.run] at same ⊢
      rw [← same]
  | weaken source bounded ih => exact ih state seed

theorem Program.total_positive {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) :
    SimulatorRejectionCost.PositiveWidths (program.total sparse attempts state) := by
  induction program generalizing state with
  | pure => trivial
  | query request next ih =>
      exact SimulatorRejectionCost.positive_bind _ _ (totalDraw_positive _ _) (fun answer => ih answer.1 answer.2)
  | map f source ih => exact SimulatorRejectionCost.positive_bind _ _ (ih state) (fun _ => trivial)
  | bind source next first second =>
      exact SimulatorRejectionCost.positive_bind _ _ (first state) (fun answer => second answer.1 answer.2)
  | weaken source bounded ih => exact ih state

/-- The total finite program has the same strict bit budget as its aborting form. -/
theorem Program.total_bits {oracle : OracleSpec.{0, 0}} {A State Seed : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (bounded : ∀ query state, drawSizeLe (2 ^ 256) (sparse query state))
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (program : Program oracle A budget) (state : State) (seed : Seed) :
    ((program.total sparse attempts state).run random seed).2 ≤ budget * (257 * attempts) := by
  induction program generalizing state seed with
  | pure => simp [Program.total, BitCode.run]
  | @query A budget request next ih =>
      simpa only [Program.total, BitCode.bind_run, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add (totalDraw_bits random attempts _ (bounded request state) seed)
          (ih ((totalDraw attempts (sparse request state)).run random seed).1.1.1
            ((totalDraw attempts (sparse request state)).run random seed).1.1.2
            ((totalDraw attempts (sparse request state)).run random seed).1.2)
  | map f source ih => simpa only [Program.total, BitCode.bind_run, BitCode.run, Nat.add_zero] using ih state seed
  | bind source next first second =>
      simpa only [Program.total, BitCode.bind_run, Nat.add_mul] using Nat.add_le_add
        (first state seed) (second ((source.total sparse attempts state).run random seed).1.1.1
          ((source.total sparse attempts state).run random seed).1.1.2
          ((source.total sparse attempts state).run random seed).1.2)
  | weaken source bounded ih => exact (ih state seed).trans (Nat.mul_le_mul_right _ bounded)


namespace Cost

/-- The total executor records sparse work and fair bits in one execution. -/
def executeTotalCost {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed) (depth : Nat) :
    (A × SparseState × Seed) × Nat × Nat × Nat :=
  let result := executeCost (totalRandom (countedSource random) attempts) program state (seed, 0) depth
  ((result.1.1, result.1.2.1, result.1.2.2.1), result.2.1, result.2.2, result.1.2.2.2)

/-- The counted executor preserves the total finite result, state, seed, and fair bits. -/
theorem executeTotalCost_correct {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed) (depth : Nat) :
    let result := (program.total combinedDraw attempts state).run random seed
    (executeTotalCost random attempts program state seed depth).1 =
      (result.1.1.1, result.1.1.2, result.1.2) ∧
    (executeTotalCost random attempts program state seed depth).2.2.2 = result.2 := by
  have same := Program.total_run combinedDraw (countedSource random) attempts program state (seed, 0)
  rw [run_countedSource] at same
  simp only [Nat.zero_add] at same
  have counted := (executeCost_correct (totalRandom (countedSource random) attempts)
    program state (seed, 0) depth).1.trans same.symm
  simp only [executeTotalCost, counted]
  constructor <;> first | rfl | trivial

/-- The total execution preserves its sparse state and its query and work bounds. -/
theorem executeTotalCost_resources {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed)
    (depth capacity : Nat) (bound : StateBound state capacity) (depthBound : depth ≤ capacity) :
    (executeTotalCost random attempts program state seed depth).2.1 ≤ budget ∧
    (executeTotalCost random attempts program state seed depth).2.2.1 ≤
      budget * (10 * (capacity + budget) + 16) ∧
    Nonempty (StateBound (executeTotalCost random attempts program state seed depth).1.2.1
      (capacity + budget)) := by
  obtain ⟨calls, work⟩ := executeCost_budget (totalRandom (countedSource random) attempts)
    program state (seed, 0) depth capacity bound depthBound
  obtain ⟨certificate⟩ := (executeCost_resources (totalRandom (countedSource random) attempts)
    program state (seed, 0) depth capacity bound depthBound).1
  exact ⟨calls, work, ⟨certificate.mono (Nat.add_le_add_left calls capacity)⟩⟩

/-- The total executor has a strict bound on its recorded fair-bit reads. -/
theorem executeTotalCost_bits {A Seed : Type} {budget : Nat}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat)
    (program : Program combinedSpec A budget) (state : SparseState) (seed : Seed) (depth : Nat) :
    (executeTotalCost random attempts program state seed depth).2.2.2 ≤ budget * (257 * attempts) := by
  rw [(executeTotalCost_correct random attempts program state seed depth).2]
  apply Program.total_bits
  intro query state
  cases same : combinedDraw query state with
  | pure => trivial
  | uniform size positive next =>
      have bounded := combinedDraw_bound query state
      simpa only [same, drawBound, drawSizeLe] using bounded

end Cost

end SimulatorMachine
end Kriterion.ArgoMAC.Security
