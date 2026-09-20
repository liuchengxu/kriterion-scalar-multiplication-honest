import Proof.Privacy.Simulator.Arithmetic.AdaptiveCutoff
import Proof.Shared.SourceHCoefficient

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.BoundedIntegerSampling Security.SimulatorSampling
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An exact source lifted into optional results has its original accepted mass. -/
theorem mapSome_apply {A : Type} (source : PMF A) (value : A) :
    (source.map some) (some value) = source value := by
  simp [PMF.map_apply]

/-- The family cuts off permutation draws and keeps hash draws exact. -/
def oracleFamilyCutoff (attempts : Nat) (query : oracleFamilySpec.Query) (state : SparseOracleFamily) :
    PMF (Option (oracleFamilySpec.Answer query × SparseOracleFamily)) :=
  match query with
  | .inl request => drawCutoffLaw attempts (oracleFamilyDraw (.inl request) state)
  | .inr key => (oracleFamilySampled (.inr key) state).map some

/-- Each family step retains the specified lower fraction of its exact joint mass. -/
theorem oracleFamilyCutoff_lower (attempts : Nat) (query : oracleFamilySpec.Query)
    (state : SparseOracleFamily) (result : oracleFamilySpec.Answer query × SparseOracleFamily) :
    retained attempts * oracleFamilySampled query state result ≤ oracleFamilyCutoff attempts query state (some result) := by
  cases query with
  | inl query => exact drawCutoffLaw_lower attempts (oracleFamilyDraw (.inl query) state) result
  | inr key =>
      rw [oracleFamilyCutoff, mapSome_apply]
      exact mul_le_of_le_one_left' tsub_le_self

/-- Each family cutoff step preserves the exact upper bound on accepted mass. -/
theorem oracleFamilyCutoff_upper (attempts : Nat) (query : oracleFamilySpec.Query)
    (state : SparseOracleFamily) (result : oracleFamilySpec.Answer query × SparseOracleFamily) :
    oracleFamilyCutoff attempts query state (some result) ≤ oracleFamilySampled query state result := by
  cases query with
  | inl query => exact drawCutoffLaw_upper attempts (oracleFamilyDraw (.inl query) state) result
  | inr key => rw [oracleFamilyCutoff, mapSome_apply]

/-- Every complete family program retains the joint source law up to its query cutoff loss. -/
theorem oracleFamilyCutoff_program_lower (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram oracleFamilySpec Result budget) (state : SparseOracleFamily) (result : Result × SparseOracleFamily) :
    retained attempts ^ budget * runSampled oracleFamilySampled program state result ≤
      runSampledCutoff (oracleFamilyCutoff attempts) program state (some result) :=
  runSampledCutoff_lower oracleFamilySampled (oracleFamilyCutoff attempts) (retained attempts) tsub_le_self
    (oracleFamilyCutoff_lower attempts) program state result

/-- The complete family program has a linear bound on its cutoff failure. -/
theorem oracleFamilyCutoff_program_failure (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram oracleFamilySpec Result budget) (state : SparseOracleFamily) :
    runSampledCutoff (oracleFamilyCutoff attempts) program state none ≤ budget * (2 : ENNReal)⁻¹ ^ attempts :=
  (runSampledCutoff_failure oracleFamilySampled (oracleFamilyCutoff attempts) (retained attempts) tsub_le_self
    (oracleFamilyCutoff_lower attempts) program state).trans
      (loss_pow_le _ (pow_le_one₀ zero_le (by norm_num)) budget)

/-- The family cutoff changes every complete adaptive event by at most its total failure allowance. -/
theorem oracleFamilyCutoff_program_event (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram oracleFamilySpec Result budget) (state : SparseOracleFamily)
    (event : Set (Option (Result × SparseOracleFamily))) :
    |((runSampledCutoff (oracleFamilyCutoff attempts) program state).toOuterMeasure event).toReal -
      (((runSampled oracleFamilySampled program state).map some).toOuterMeasure event).toReal| ≤
      budget * (2 : ℝ)⁻¹ ^ attempts := by
  let ideal := (runSampled oracleFamilySampled program state).map some
  have retainedBound : retained attempts ^ budget ≤ 1 := pow_le_one₀ zero_le tsub_le_self
  have bound := Security.hCoefficient_event_of_goodSubmass
    (runSampledCutoff (oracleFamilyCutoff attempts) program state) ideal ideal
    (1 - retained attempts ^ budget) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) 0
    (fun _ => le_rfl) (by simp) (fun result => ?_) event
  · apply bound.trans
    rw [zero_add]
    have loss := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top budget) (by finiteness))
      (loss_pow_le ((2 : ENNReal)⁻¹ ^ attempts) (pow_le_one₀ zero_le (by norm_num)) budget)
    simpa only [retained, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat] using loss
  · rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top retainedBound]
    cases result with
    | none => simp [ideal, PMF.map_apply]
    | some result =>
        rw [show ideal (some result) = runSampled oracleFamilySampled program state result from mapSome_apply _ _]
        exact oracleFamilyCutoff_program_lower attempts program state result

end
end Kriterion.ArgoMAC.ArithmeticSimulator
