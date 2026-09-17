import Proof.Privacy.Simulator.SimulatorCutoff

namespace Kriterion.ArgoMAC.Security.SimulatorRejectionCost
open Cryptography BoundedIntegerSampling SimulatorSampling SimulatorMachine OperationalOracle

/-- This condition excludes zero-width random instructions on every branch. -/
def PositiveWidths {A : Type} : BitCode A → Prop
  | .pure _ => True
  | .bits width next => 0 < width ∧ ∀ value, PositiveWidths (next value)

/-- This interpreter counts fair bits, sampled blocks, and four control operations per block.
The control charge covers the range test, result branch, retry step, and dispatch.
Other deterministic callbacks have their own local counters. -/
def runWithCost {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) :
    BitCode A → Seed → ((A × Seed) × Nat) × Nat × Nat
  | .pure value, seed => (((value, seed), 0), 0, 0)
  | .bits width next, seed =>
      let sampled := random width seed
      let tail := runWithCost random (next sampled.1) sampled.2
      ((tail.1.1, width + tail.1.2), tail.2.1 + 1, tail.2.2 + 4)

/-- The counted interpreter preserves the value, seed, and exact fair-bit count. -/
theorem runWithCost_value {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (seed : Seed) :
    (runWithCost random code seed).1 = code.run random seed := by
  induction code generalizing seed with
  | pure => rfl
  | bits width next ih => simp only [runWithCost, BitCode.run, ih]

/-- Each positive-width block contains at least one counted fair bit. -/
theorem runWithCost_blocks {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (positive : PositiveWidths code) (seed : Seed) :
    (runWithCost random code seed).2.1 ≤ (runWithCost random code seed).1.2 := by
  induction code generalizing seed with
  | pure => exact Nat.le_refl _
  | bits width next ih =>
      have tail := ih (random width seed).1 (positive.2 _) (random width seed).2
      have widthPositive := positive.1
      simp only [runWithCost]
      omega

/-- The control charge is exactly four times the number of executed blocks. -/
theorem runWithCost_control {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (seed : Seed) :
    (runWithCost random code seed).2.2 = 4 * (runWithCost random code seed).2.1 := by
  induction code generalizing seed with
  | pure => rfl
  | bits width next ih =>
      have tail := ih (random width seed).1 (random width seed).2
      simp only [runWithCost]
      omega

/-- The same fair-bit bound controls rejection work on success and failure paths. -/
theorem runWithCost_bound {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (code : BitCode A) (positive : PositiveWidths code) (seed : Seed) :
    (runWithCost random code seed).2.2 ≤ 4 * (code.run random seed).2 := by
  rw [runWithCost_control]
  have bound := Nat.mul_le_mul_left 4 (runWithCost_blocks random code positive seed)
  rwa [runWithCost_value] at bound

/-- Adaptive composition preserves positive widths. -/
theorem positive_bind {A B : Type} (source : BitCode A) (next : A → BitCode B)
    (first : PositiveWidths source) (second : ∀ value, PositiveWidths (next value)) :
    PositiveWidths (source.bind next) := by
  induction source with
  | pure value => exact second value
  | bits width branch ih => exact ⟨first.1, fun value => ih value (first.2 value)⟩

/-- The rejection width is positive for every finite range. -/
theorem cutoff_positive (size attempts : Nat) :
    PositiveWidths (cutoff size attempts) := by
  induction attempts with
  | zero => trivial
  | succ attempts ih =>
      refine ⟨by unfold width; omega, ?_⟩
      intro value
      dsimp only
      split <;> trivial

/-- Every finite private sampler uses only positive-width rejection blocks. -/
theorem code_cutoff_positive {A : Type} {count : Nat} (code : Code A count) (attempts : Nat) :
    PositiveWidths (code.cutoff attempts) := by
  induction code with
  | pure => trivial
  | draw size positive => exact cutoff_positive size attempts
  | bind source next first second =>
      simp only [Code.cutoff]
      apply positive_bind _ _ first
      intro value
      cases value with
      | none => trivial
      | some value => exact second value

/-- A failed draw stops without introducing another random instruction. -/
theorem optional_positive {A B : Type} (next : A → BitCode (Option B))
    (positive : ∀ value, PositiveWidths (next value)) (value : Option A) :
    PositiveWidths (optional next value) := by
  cases value with
  | none => trivial
  | some value => exact positive value

/-- Every sparse oracle draw uses a positive-width rejection block. -/
theorem draw_positive {A : Type} (attempts : Nat) (draw : Draw A) :
    PositiveWidths (cutoffDraw attempts draw) := by
  cases draw with
  | pure => trivial
  | uniform size positive next => exact code_cutoff_positive _ _

/-- Every finite oracle program preserves positive widths through all continuations. -/
theorem program_positive {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) :
    PositiveWidths (program.cutoff sparse attempts state) := by
  induction program generalizing state with
  | pure => trivial
  | query request next ih =>
      apply positive_bind _ _ (draw_positive _ _)
      exact optional_positive _ (fun answer => ih answer.1 answer.2)
  | map f source ih =>
      apply positive_bind _ _ (ih state)
      exact optional_positive _ (fun _ => trivial)
  | bind source next first second =>
      apply positive_bind _ _ (first state)
      exact optional_positive _ (fun answer => second answer.1 answer.2)
  | weaken source bounded ih => exact ih state

end Kriterion.ArgoMAC.Security.SimulatorRejectionCost
