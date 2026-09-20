import Proof.Privacy.Simulator.Arithmetic.OracleFamilyLaw
import Proof.Privacy.Simulator.SamplingCutoff
import Proof.Shared.SourceHCoefficient

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.BoundedIntegerSampling Security.SimulatorSampling
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An absent source result stops the remaining adaptive program. -/
def bindCutoff {A B : Type} (source : PMF (Option A)) (next : A → PMF (Option B)) : PMF (Option B) :=
  source.bind fun result => match result with
    | none => PMF.pure none
    | some value => next value

/-- The cutoff interpreter stops at the first absent oracle result. -/
def runSampledCutoff {oracle : OracleSpec} {Result State : Type}
    (handler : ∀ query, State → PMF (Option (oracle.Answer query × State))) :
    {budget : Nat} → OracleProgram oracle Result budget → State → PMF (Option (Result × State))
  | _, .pure distribution, state => distribution.map (fun value => some (value, state))
  | _, .query request next, state => bindCutoff (handler request state)
      (fun result => runSampledCutoff handler (next result.1) result.2)
  | _, .sample distribution next, state => distribution.bind (fun value => runSampledCutoff handler (next value) state)

/-- The optional sum separates failure from every accepted result. -/
theorem cutoff_tsum_option {A : Type} (function : Option A → ENNReal) :
    (∑' value, function value) = function none + ∑' value, function (some value) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} A).symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp [add_comm]

/-- A cutoff continuation's accepted mass uses only accepted source results. -/
theorem bindCutoff_some {A B : Type} (source : PMF (Option A)) (next : A → PMF (Option B)) (value : B) :
    bindCutoff source next (some value) = ∑' input, source (some input) * next input (some value) := by
  rw [bindCutoff, PMF.bind_apply, cutoff_tsum_option]
  simp

/-- Mapping optional values retains the accepted source mass at each preimage. -/
theorem mapCutoff_some {A B : Type} (source : PMF (Option A)) (convert : A → B) (value : B) :
    (source.map (Option.map convert)) (some value) =
      ∑' input, if value = convert input then source (some input) else 0 := by
  classical
  rw [PMF.map_apply, cutoff_tsum_option]
  simp

/-- Every finite draw retains a uniform lower fraction of its exact source mass. -/
theorem drawCutoffLaw_lower {A : Type} (attempts : Nat) (draw : Draw A) (value : A) :
    retained attempts * draw.distribution value ≤ drawCutoffLaw attempts draw (some value) := by
  classical
  cases draw with
  | pure item =>
      simp only [Draw.distribution, drawCutoffLaw, PMF.pure_apply, Option.some.injEq]
      split <;> simp_all [retained, tsub_le_self]
  | uniform bound positive next =>
      simp only [Draw.distribution, drawCutoffLaw]
      rw [mapCutoff_some, PMF.map_apply]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro input
      split
      · rw [cutoff_success_submass bound positive]
        exact mul_le_mul_left (tsub_le_tsub_left
          (pow_le_pow_left' (rejection_le_half bound positive) attempts) 1) _
      · simp

/-- The cutoff draw never increases an accepted result's exact source mass. -/
theorem drawCutoffLaw_upper {A : Type} (attempts : Nat) (draw : Draw A) (value : A) :
    drawCutoffLaw attempts draw (some value) ≤ draw.distribution value := by
  classical
  cases draw with
  | pure item => simp [Draw.distribution, drawCutoffLaw, PMF.pure_apply]
  | uniform bound positive next =>
      simp only [Draw.distribution, drawCutoffLaw]
      rw [mapCutoff_some, PMF.map_apply]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      apply ENNReal.tsum_le_tsum
      intro input
      split
      · rw [cutoff_success_submass bound positive]
        exact mul_le_of_le_one_left' tsub_le_self
      · exact le_rfl

/-- Each adaptive query pays at most one retained fraction, including all state changes. -/
theorem runSampledCutoff_lower {oracle : OracleSpec} {Result State : Type}
    (exact : ∀ query, State → PMF (oracle.Answer query × State))
    (cutoff : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (factor : ENNReal) (bounded : factor ≤ 1)
    (step : ∀ query state result, factor * exact query state result ≤ cutoff query state (some result))
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) (result : Result × State) :
    factor ^ budget * runSampled exact program state result ≤ runSampledCutoff cutoff program state (some result) := by
  classical
  induction program generalizing state with
  | @pure budget distribution =>
      simp only [runSampled, runSampledCutoff, PMF.map_apply, Option.some.injEq]
      convert (mul_le_of_le_one_left' (a := (distribution.map (fun value => (value, state))) result)
        (show factor ^ budget ≤ 1 from pow_le_one₀ zero_le bounded)) using 1 <;> try simp only [PMF.map_apply]
      all_goals first | rfl | (apply tsum_congr; intro value; exact (ite_eq_ite _ _ _).mpr trivial)
  | @query budget query next ih =>
      simp only [runSampled, runSampledCutoff, bindCutoff_some, PMF.bind_apply, pow_succ]
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro answer
      calc
        _ = (factor * exact query state answer) *
            (factor ^ budget * runSampled exact (next answer.1) answer.2 result) := by ac_rfl
        _ ≤ _ := mul_le_mul' (step query state answer) (ih answer.1 answer.2)
  | sample distribution next ih =>
      simp only [runSampled, runSampledCutoff, PMF.bind_apply]
      rw [← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro value
      calc
        _ = distribution value * (factor ^ _ * runSampled exact (next value) state result) := by ac_rfl
        _ ≤ _ := mul_le_mul_right (ih value state) _

/-- Each accepted adaptive result has no more mass than its exact source result. -/
theorem runSampledCutoff_upper {oracle : OracleSpec} {Result State : Type}
    (exact : ∀ query, State → PMF (oracle.Answer query × State))
    (cutoff : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (step : ∀ query state result, cutoff query state (some result) ≤ exact query state result)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) (result : Result × State) :
    runSampledCutoff cutoff program state (some result) ≤ runSampled exact program state result := by
  classical
  induction program generalizing state with
  | pure distribution =>
      simp only [runSampled, runSampledCutoff, PMF.map_apply, Option.some.injEq]
      convert (le_refl ((distribution.map (fun value => (value, state))) result)) using 1 <;> try simp only [PMF.map_apply]
      all_goals first | rfl | (apply tsum_congr; intro value; exact (ite_eq_ite _ _ _).mpr trivial)
  | query query next ih =>
      simp only [runSampled, runSampledCutoff, bindCutoff_some, PMF.bind_apply]
      exact ENNReal.tsum_le_tsum fun answer => mul_le_mul' (step query state answer) (ih answer.1 answer.2)
  | sample distribution next ih =>
      simp only [runSampled, runSampledCutoff, PMF.bind_apply]
      exact ENNReal.tsum_le_tsum fun value => mul_le_mul_right (ih value state) _

/-- The complete adaptive cutoff failure is at most the missing retained fraction. -/
theorem runSampledCutoff_failure {oracle : OracleSpec} {Result State : Type}
    (exact : ∀ query, State → PMF (oracle.Answer query × State))
    (cutoff : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (factor : ENNReal) (bounded : factor ≤ 1)
    (step : ∀ query state result, factor * exact query state result ≤ cutoff query state (some result))
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    runSampledCutoff cutoff program state none ≤ 1 - factor ^ budget := by
  have total := (runSampledCutoff cutoff program state).tsum_coe
  rw [cutoff_tsum_option] at total
  have lower : factor ^ budget ≤ ∑' value, runSampledCutoff cutoff program state (some value) := by
    calc
      _ = factor ^ budget * ∑' value, runSampled exact program state value := by
        rw [(runSampled exact program state).tsum_coe, mul_one]
      _ = ∑' value, factor ^ budget * runSampled exact program state value := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun value => runSampledCutoff_lower exact cutoff factor bounded step program state value
  exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top total).le.trans (tsub_le_tsub_left lower 1)

/-- A complete adaptive cutoff changes every event by at most its missing retained fraction. -/
theorem runSampledCutoff_event_bound {oracle : OracleSpec} {Result State : Type}
    (exact : ∀ query, State → PMF (oracle.Answer query × State))
    (cutoff : ∀ query, State → PMF (Option (oracle.Answer query × State)))
    (factor : ENNReal) (bounded : factor ≤ 1)
    (step : ∀ query state result, factor * exact query state result ≤ cutoff query state (some result))
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State)
    (event : Set (Option (Result × State))) :
    |((runSampledCutoff cutoff program state).toOuterMeasure event).toReal -
      (((runSampled exact program state).map some).toOuterMeasure event).toReal| ≤
      (1 - factor ^ budget).toReal := by
  let ideal := (runSampled exact program state).map some
  have retainedBound : factor ^ budget ≤ 1 := pow_le_one₀ zero_le bounded
  have bound := Security.hCoefficient_event_of_goodSubmass
    (runSampledCutoff cutoff program state) ideal ideal
    (1 - factor ^ budget) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) 0
    (fun _ => le_rfl) (by simp) (fun result => ?_) event
  · simpa only [zero_add] using bound
  · rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top retainedBound]
    cases result with
    | none => simp [ideal, PMF.map_apply]
    | some result =>
        have same : ideal (some result) = runSampled exact program state result := by simp [ideal]
        rw [same]
        exact runSampledCutoff_lower exact cutoff factor bounded step program state result

end
end Kriterion.ArgoMAC.ArithmeticSimulator
