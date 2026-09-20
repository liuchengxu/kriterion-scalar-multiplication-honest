import Proof.Privacy.Simulator.Arithmetic.AdaptiveCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography
noncomputable section

/-- A projection commutes with cutoff bind when each accepted continuation has the stated marginal. -/
theorem cutoff_map_bind {A B C D : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (input : A → C) (output : B → D) (target : C → PMF (Option D))
    (law : ∀ value, some value ∈ source.support → (next value).map (Option.map output) = target (input value)) :
    (bindCutoff source next).map (Option.map output) =
      bindCutoff (source.map (Option.map input)) target := by
  simp only [bindCutoff, PMF.map_bind, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  cases result with
  | none => simp only [PMF.pure_map, Option.map_none, Function.comp_def]
  | some value => exact law value supported

/-- Each accepted cutoff continuation comes from an accepted first result. -/
theorem mem_support_bindCutoff {A B : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (result : B) :
    some result ∈ (bindCutoff source next).support ↔
      ∃ value, some value ∈ source.support ∧ some result ∈ (next value).support := by
  constructor
  · intro supported
    obtain ⟨value, reached, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    cases value with
    | none => simp only [PMF.mem_support_pure_iff, Option.some_ne_none] at supported
    | some value => exact ⟨value, reached, supported⟩
  · rintro ⟨value, reached, supported⟩
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨some value, reached, supported⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
