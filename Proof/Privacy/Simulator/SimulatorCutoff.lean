import Proof.Privacy.Simulator.SimulatorRuntime

namespace Kriterion.ArgoMAC.Security
open Cryptography OperationalOracle SimulatorSampling BoundedIntegerSampling
open scoped ENNReal
namespace SimulatorMachine

/-- The finite draw sampler retains the exact deterministic continuation. -/
def cutoffDraw {A : Type} (attempts : Nat) : Draw A → BitCode (Option A)
  | .pure value => .pure (some value)
  | .uniform size positive next => ((Code.draw size positive).map next).cutoff attempts

theorem cutoffDraw_lower {A : Type} (attempts : Nat) (draw : Draw A) (value : A) :
    retained attempts * draw.distribution value ≤ (cutoffDraw attempts draw).law (some value) := by
  classical
  cases draw with
  | pure item =>
      have bounded : retained attempts ≤ 1 := tsub_le_self
      simpa only [Draw.distribution, cutoffDraw, BitCode.law, PMF.pure_apply, Option.some.injEq,
        one_mul] using mul_le_mul_left bounded ((PMF.pure item) value)
  | uniform size positive next =>
      simpa only [cutoffDraw, Code.map_law, Code.law, Draw.distribution, pow_one] using
        ((Code.draw size positive).map next).cutoff_lower attempts value

theorem cutoffDraw_upper {A : Type} (attempts : Nat) (draw : Draw A) (value : A) :
    (cutoffDraw attempts draw).law (some value) ≤ draw.distribution value := by
  classical
  cases draw with
  | pure item => simp only [cutoffDraw, BitCode.law, Draw.distribution, PMF.pure_apply,
      Option.some.injEq, le_refl]
  | uniform size positive next =>
      simpa only [cutoffDraw, Code.map_law, Code.law, Draw.distribution] using
        ((Code.draw size positive).map next).cutoff_upper attempts value

/-- This continuation stops the program after a failed integer draw. -/
def optional {A B : Type} (next : A → BitCode (Option B)) : Option A → BitCode (Option B)
  | none => .pure none
  | some value => next value

private theorem optional_law {A B : Type} (next : A → BitCode (Option B)) (value : Option A) :
    (optional next value).law =
      match value with | none => PMF.pure none | some item => (next item).law := by
  cases value <;> rfl

private theorem tsum_option {A : Type} (f : Option A → ENNReal) :
    (∑' value, f value) = f none + ∑' value, f (some value) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} A).symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp [add_comm]

private theorem optional_bind_apply {A B : Type} (source : BitCode (Option A))
    (next : A → BitCode (Option B)) (value : B) :
    (source.bind (optional next)).law (some value) =
      ∑' item, source.law (some item) * (next item).law (some value) := by
  rw [BitCode.bind_law, PMF.bind_apply, tsum_option]
  simp only [optional, BitCode.law, PMF.pure_apply, reduceCtorEq, if_false, mul_zero, zero_add]

theorem optional_bind_lower {A B : Type}
    (source : BitCode (Option A)) (next : A → BitCode (Option B))
    (exactSource : PMF A) (exactNext : A → PMF B) (first second : ENNReal)
    (left : ∀ value, first * exactSource value ≤ source.law (some value))
    (right : ∀ item value, second * exactNext item value ≤ (next item).law (some value))
    (value : B) :
    (first * second) * (exactSource.bind exactNext) value ≤
      (source.bind (optional next)).law (some value) := by
  rw [optional_bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro item
  calc
    (first * second) * (exactSource item * exactNext item value) =
        (first * exactSource item) * (second * exactNext item value) := by ac_rfl
    _ ≤ _ := mul_le_mul' (left item) (right item value)

theorem optional_bind_upper {A B : Type}
    (source : BitCode (Option A)) (next : A → BitCode (Option B))
    (exactSource : PMF A) (exactNext : A → PMF B)
    (left : ∀ value, source.law (some value) ≤ exactSource value)
    (right : ∀ item value, (next item).law (some value) ≤ exactNext item value) (value : B) :
    (source.bind (optional next)).law (some value) ≤ (exactSource.bind exactNext) value := by
  rw [optional_bind_apply, PMF.bind_apply]
  exact ENNReal.tsum_le_tsum fun item => mul_le_mul' (left item) (right item value)

/-- This executable program gives every sparse integer draw a finite retry limit. -/
def Program.cutoff {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) : Program oracle A budget → State → BitCode (Option (A × State))
  | .pure value, state => .pure (some (value, state))
  | .query request next, state => (cutoffDraw attempts (sparse request state)).bind
      (optional fun answer => (next answer.1).cutoff sparse attempts answer.2)
  | .map f source, state => (source.cutoff sparse attempts state).bind
      (optional fun answer => .pure (some (f answer.1, answer.2)))
  | .bind source next, state => (source.cutoff sparse attempts state).bind
      (optional fun answer => (next answer.1).cutoff sparse attempts answer.2)
  | .weaken source _, state => source.cutoff sparse attempts state

/-- The finite simulator retains a uniform fraction of its exact joint output law. -/
theorem Program.cutoff_lower {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) (value : A × State) :
    retained attempts ^ budget * program.sampledLaw sparse state value ≤
      (program.cutoff sparse attempts state).law (some value) := by
  classical
  induction program generalizing state with
  | pure item => simp [Program.cutoff, Program.sampledLaw, BitCode.law, PMF.pure_apply, Option.some.injEq]
  | @query A budget request next ih =>
      simp only [Program.cutoff, Program.sampledLaw, pow_succ]
      rw [mul_comm (retained attempts ^ budget) (retained attempts)]
      apply optional_bind_lower
      · exact cutoffDraw_lower attempts (sparse request state)
      · intro answer value
        exact ih answer.1 answer.2 value
  | map f source ih =>
      simpa only [Program.cutoff, Program.sampledLaw, mul_one, PMF.map] using
        optional_bind_lower _ _ _ _ _ 1 (ih state)
          (fun answer value => by simp [BitCode.law, PMF.pure_apply, Option.some.injEq]) value
  | bind source next first second =>
      simpa only [Program.cutoff, Program.sampledLaw, pow_add] using
        optional_bind_lower _ _ _ _ _ _ (first state) (fun answer => second answer.1 answer.2) value
  | weaken source bounded ih =>
      exact (mul_le_mul_left (pow_le_pow_right_of_le_one' (tsub_le_self : retained attempts ≤ 1)
        bounded) _).trans (ih state value)

/-- The finite simulator does not add mass to a successful joint output. -/
theorem Program.cutoff_upper {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) (value : A × State) :
    (program.cutoff sparse attempts state).law (some value) ≤ program.sampledLaw sparse state value := by
  classical
  induction program generalizing state with
  | pure item => simp [Program.cutoff, Program.sampledLaw, BitCode.law, PMF.pure_apply, Option.some.injEq]; split_ifs <;> norm_num
  | query request next ih =>
      apply optional_bind_upper
      · exact cutoffDraw_upper attempts (sparse request state)
      · intro answer value
        exact ih answer.1 answer.2 value
  | map f source ih =>
      exact optional_bind_upper _ _ _ _ (ih state)
        (fun answer value => by simp [BitCode.law, PMF.pure_apply, Option.some.injEq]; split_ifs <;> norm_num) value
  | bind source next first second =>
      exact optional_bind_upper _ _ _ _ (first state) (fun answer => second answer.1 answer.2) value
  | weaken source bounded ih => exact ih state value

/-- The complete finite simulator fails with probability at most its operation budget times the draw loss. -/
theorem Program.cutoff_failure {oracle : OracleSpec.{0, 0}} {A State : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (attempts : Nat) (program : Program oracle A budget) (state : State) :
    (program.cutoff sparse attempts state).law none ≤ budget * (2 : ENNReal)⁻¹ ^ attempts := by
  have total := (program.cutoff sparse attempts state).law.tsum_coe
  rw [tsum_option] at total
  have lower : retained attempts ^ budget ≤
      ∑' value, (program.cutoff sparse attempts state).law (some value) := by
    calc
      retained attempts ^ budget =
          retained attempts ^ budget * ∑' value, program.sampledLaw sparse state value := by
        rw [(program.sampledLaw sparse state).tsum_coe, mul_one]
      _ = _ := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun value => program.cutoff_lower sparse attempts state value
  exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top total).le.trans
    ((tsub_le_tsub_left lower 1).trans
      (loss_pow_le _ (pow_le_one₀ zero_le (by norm_num)) budget))

theorem optional_bit_bound {A B Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (source : BitCode (Option A)) (next : A → BitCode (Option B))
    (first second : Nat) (left : ∀ seed, (source.run random seed).2 ≤ first)
    (right : ∀ value seed, ((next value).run random seed).2 ≤ second) (seed : Seed) :
    ((source.bind (optional next)).run random seed).2 ≤ first + second := by
  rw [BitCode.bind_run]
  simp only [optional]
  split
  · simpa only [BitCode.run, Nat.add_zero] using (left seed).trans (Nat.le_add_right first second)
  · rename_i value same
    exact Nat.add_le_add (left seed) (right value (source.run random seed).1.2)

/-- This predicate restricts the size of the primitive integer draw. -/
def drawSizeLe {A : Type} (maximum : Nat) : Draw A → Prop
  | .pure _ => True
  | .uniform size _ _ => size ≤ maximum

theorem cutoffDraw_bit_bound {A Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (draw : Draw A) (bounded : drawSizeLe (2 ^ 256) draw) (seed : Seed) :
    ((cutoffDraw attempts draw).run random seed).2 ≤ 257 * attempts := by
  cases draw with
  | pure => simp [cutoffDraw, BitCode.run]
  | uniform size positive next =>
      simpa only [cutoffDraw, Nat.one_mul] using
        ((Code.draw size positive).map next).cutoff_bit_bound random attempts
        (Code.map_drawSizeLe _ _ bounded) seed

/-- The finite simulator has a strict bound on its actual fair-bit reads. -/
theorem Program.cutoff_bit_bound {oracle : OracleSpec.{0, 0}} {A State Seed : Type} {budget : Nat}
    (sparse : (query : oracle.Query) → State → Draw (oracle.Answer query × State))
    (bounded : ∀ query state, drawSizeLe (2 ^ 256) (sparse query state))
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (program : Program oracle A budget) (state : State) (seed : Seed) :
    ((program.cutoff sparse attempts state).run random seed).2 ≤ budget * (257 * attempts) := by
  induction program generalizing state seed with
  | pure => simp [Program.cutoff, BitCode.run]
  | @query A budget request next ih =>
      simpa only [Program.cutoff, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        optional_bit_bound random _ _ (257 * attempts) (budget * (257 * attempts))
          (cutoffDraw_bit_bound random attempts _ (bounded request state))
          (fun answer seed => ih answer.1 answer.2 seed) seed
  | map f source ih =>
      simpa only [Program.cutoff, Nat.add_zero] using
        optional_bit_bound random _ _ _ 0 (ih state)
          (fun answer seed => by simp [BitCode.run]) seed
  | @bind A B first second source next ihSource ihNext =>
      simpa only [Program.cutoff, Nat.add_mul] using
        optional_bit_bound random _ _ _ _ (ihSource state)
          (fun answer seed => ihNext answer.1 answer.2 seed) seed
  | weaken source budgetBound ih =>
      exact (ih state seed).trans (Nat.mul_le_mul_right _ budgetBound)

end SimulatorMachine
end Kriterion.ArgoMAC.Security
