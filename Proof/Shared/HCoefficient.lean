import Cryptography.Assumptions
import Mathlib.Tactic.Linarith

namespace Kriterion.ArgoMAC.Security

/-- The ideal bad mass and weighted deficit bound every transcript event. -/
theorem hCoefficient_event_of_deficit {Transcript : Type*}
    (real ideal : PMF Transcript) (bad event : Set Transcript)
    (deficit : Transcript → ℝ) (deficitNonnegative : ∀ t, 0 ≤ deficit t)
    (deficitSummable : Summable
      (badᶜ.indicator (fun t => deficit t * (ideal t).toReal)))
    (goodBound : ∀ transcript ∉ bad,
      (1 - deficit transcript) * (ideal transcript).toReal ≤ (real transcript).toReal) :
    |(real.toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤
      (ideal.toOuterMeasure bad).toReal +
        ∑' t, badᶜ.indicator (fun t => deficit t * (ideal t).toReal) t := by
  classical
  let mass := fun (p : PMF Transcript) (s : Set Transcript) =>
    ∑' t, s.indicator (fun t => (p t).toReal) t
  have summable (p : PMF Transcript) : Summable (fun t => (p t).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; simp)
  have mass_eq (p : PMF Transcript) (s : Set Transcript) :
      mass p s = (p.toOuterMeasure s).toReal := by
    rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
    · apply tsum_congr
      intro t
      by_cases h : t ∈ s <;> simp [Set.indicator, h]
    · intro t
      by_cases h : t ∈ s <;> simp [Set.indicator, h, p.apply_ne_top]
  have total (p : PMF Transcript) : (∑' t, (p t).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]
    simp
  have partition (p : PMF Transcript) (s : Set Transcript) :
      mass p s + mass p sᶜ = 1 := by
    rw [← Summable.tsum_add ((summable p).indicator s) ((summable p).indicator sᶜ),
      ← total p]
    apply tsum_congr
    intro t
    by_cases h : t ∈ s <;> simp [Set.indicator, h]
  let loss := badᶜ.indicator (fun t => deficit t * (ideal t).toReal)
  have bound (s : Set Transcript) :
      mass ideal s ≤ mass real s + mass ideal bad + ∑' t, loss t := by
    have pointwise : ∀ t,
        s.indicator (fun t => (ideal t).toReal) t ≤
          s.indicator (fun t => (real t).toReal) t +
            bad.indicator (fun t => (ideal t).toReal) t + loss t := by
      intro t
      have hn : 0 ≤ deficit t * (ideal t).toReal :=
        mul_nonneg (deficitNonnegative t) ENNReal.toReal_nonneg
      by_cases hs : t ∈ s <;> by_cases hb : t ∈ bad
      · simp [loss, Set.indicator, hs, hb]
      · simp only [loss, Set.indicator_of_mem hs, Set.indicator_of_notMem hb,
          Set.indicator_of_mem (Set.mem_compl hb)]
        linarith [goodBound t hb]
      · simp [loss, Set.indicator, hs, hb]
      · simpa [loss, Set.indicator, hs, hb] using hn
    have h := Summable.tsum_le_tsum pointwise ((summable ideal).indicator s)
      ((((summable real).indicator s).add ((summable ideal).indicator bad)).add
        deficitSummable)
    rw [Summable.tsum_add (((summable real).indicator s).add ((summable ideal).indicator bad))
      deficitSummable,
      Summable.tsum_add ((summable real).indicator s) ((summable ideal).indicator bad)] at h
    exact h
  rw [← mass_eq real event, ← mass_eq ideal event, ← mass_eq ideal bad, abs_le]
  constructor
  · linarith [bound event]
  · linarith [bound eventᶜ, partition real event, partition ideal event]

/-- The constant H-coefficient assumptions bound every transcript event. -/
theorem hCoefficient_event {Transcript : Type*}
    (real ideal : PMF Transcript) (bad event : Set Transcript)
    (ε₁ ε₂ : ℝ) (errorNonnegative : 0 ≤ ε₂)
    (badBound : (ideal.toOuterMeasure bad).toReal ≤ ε₁)
    (goodBound : ∀ transcript ∉ bad,
      (1 - ε₂) * (ideal transcript).toReal ≤ (real transcript).toReal) :
    |(real.toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤
      ε₁ + ε₂ := by
  classical
  have hs : Summable (fun t => ε₂ * (ideal t).toReal) :=
    (ENNReal.summable_toReal (by rw [ideal.tsum_coe]; simp)).mul_left ε₂
  have lossBound :
      (∑' t, badᶜ.indicator (fun t => ε₂ * (ideal t).toReal) t) ≤ ε₂ := by
    calc
      _ ≤ ∑' t, ε₂ * (ideal t).toReal :=
        Summable.tsum_le_tsum (fun t => by
          by_cases h : t ∈ badᶜ <;> simp [Set.indicator, h]
          exact mul_nonneg errorNonnegative ENNReal.toReal_nonneg) (hs.indicator _) hs
      _ = ε₂ := by
        rw [tsum_mul_left, ← ENNReal.tsum_toReal_eq ideal.apply_ne_top, ideal.tsum_coe]
        simp
  exact (hCoefficient_event_of_deficit real ideal bad event (fun _ => ε₂)
    (fun _ => errorNonnegative) (hs.indicator _) goodBound).trans
    (add_le_add badBound lossBound)

/-- A Boolean output has the ideal-weighted H-coefficient bound. -/
theorem hCoefficient_advantage_of_deficit {Transcript : Type*}
    (real ideal : PMF Transcript) (bad : Set Transcript) (output : Transcript → Bool)
    (deficit : Transcript → ℝ) (deficitNonnegative : ∀ t, 0 ≤ deficit t)
    (deficitSummable : Summable
      (badᶜ.indicator (fun t => deficit t * (ideal t).toReal)))
    (goodBound : ∀ transcript ∉ bad,
      (1 - deficit transcript) * (ideal transcript).toReal ≤ (real transcript).toReal) :
    Cryptography.Assumptions.advantage (real.map output) (ideal.map output) ≤
      (ideal.toOuterMeasure bad).toReal +
        ∑' t, badᶜ.indicator (fun t => deficit t * (ideal t).toReal) t := by
  unfold Cryptography.Assumptions.advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact hCoefficient_event_of_deficit real ideal bad (output ⁻¹' {true}) deficit
    deficitNonnegative deficitSummable goodBound

/-- A Boolean transcript output has the H-coefficient advantage bound. -/
theorem hCoefficient_advantage {Transcript : Type*}
    (real ideal : PMF Transcript) (bad : Set Transcript) (output : Transcript → Bool)
    (ε₁ ε₂ : ℝ) (errorNonnegative : 0 ≤ ε₂)
    (badBound : (ideal.toOuterMeasure bad).toReal ≤ ε₁)
    (goodBound : ∀ transcript ∉ bad,
      (1 - ε₂) * (ideal transcript).toReal ≤ (real transcript).toReal) :
    Cryptography.Assumptions.advantage (real.map output) (ideal.map output) ≤ ε₁ + ε₂ := by
  unfold Cryptography.Assumptions.advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact hCoefficient_event real ideal bad (output ⁻¹' {true}) ε₁ ε₂
    errorNonnegative badBound goodBound

end Kriterion.ArgoMAC.Security
