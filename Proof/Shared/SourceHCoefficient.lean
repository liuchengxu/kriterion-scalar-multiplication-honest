import Proof.Shared.HCoefficient
import Proof.Shared.SourceGoodMass

namespace Kriterion.ArgoMAC.Security

noncomputable section

/-- A summable pointwise mass loss bounds every transcript event. -/
theorem hCoefficient_event_of_errorMass {Transcript : Type*}
    (real ideal : PMF Transcript) (loss : Transcript → ℝ)
    (nonnegative : ∀ transcript, 0 ≤ loss transcript) (summableLoss : Summable loss)
    (bound : ∀ transcript, (ideal transcript).toReal ≤ (real transcript).toReal + loss transcript)
    (event : Set Transcript) :
    |(real.toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤ ∑' t, loss t := by
  classical
  let mass := fun (p : PMF Transcript) (s : Set Transcript) =>
    ∑' t, s.indicator (fun t => (p t).toReal) t
  have summable (p : PMF Transcript) : Summable (fun t => (p t).toReal) :=
    ENNReal.summable_toReal (by rw [p.tsum_coe]; simp)
  have massEq (p : PMF Transcript) (s : Set Transcript) :
      mass p s = (p.toOuterMeasure s).toReal := by
    rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
    · apply tsum_congr
      intro t
      by_cases member : t ∈ s <;> simp [Set.indicator, member]
    · intro t
      by_cases member : t ∈ s <;> simp [Set.indicator, member, p.apply_ne_top]
  have partition (p : PMF Transcript) (s : Set Transcript) :
      mass p s + mass p sᶜ = 1 := by
    rw [← Summable.tsum_add ((summable p).indicator s) ((summable p).indicator sᶜ)]
    have total : (∑' t, (p t).toReal) = 1 := by
      rw [← ENNReal.tsum_toReal_eq p.apply_ne_top, p.tsum_coe]
      simp
    rw [← total]
    apply tsum_congr
    intro t
    by_cases member : t ∈ s <;> simp [Set.indicator, member]
  have eventBound (s : Set Transcript) : mass ideal s ≤ mass real s + ∑' t, loss t := by
    have pointwise : ∀ t, s.indicator (fun t => (ideal t).toReal) t ≤
        s.indicator (fun t => (real t).toReal) t + loss t := by
      intro t
      by_cases member : t ∈ s
      · simpa only [Set.indicator_of_mem member] using bound t
      · simpa only [Set.indicator_of_notMem member, zero_add] using nonnegative t
    exact (Summable.tsum_le_tsum pointwise ((summable ideal).indicator s)
      (((summable real).indicator s).add summableLoss)).trans_eq
        (Summable.tsum_add ((summable real).indicator s) summableLoss)
  rw [← massEq real event, ← massEq ideal event, abs_le]
  constructor
  · linarith [eventBound event]
  · linarith [eventBound eventᶜ, partition real event, partition ideal event]

/-- A good source submass gives the H-coefficient bound after hidden tags are removed. -/
theorem hCoefficient_event_of_goodSubmass {Transcript : Type*}
    (real ideal : PMF Transcript) (good : Transcript → ENNReal) (error : ENNReal)
    (errorFinite : error ≠ ⊤) (badBound : ℝ)
    (goodLe : ∀ t, good t ≤ ideal t)
    (missingBound : ENNReal.toReal (∑' t : Transcript, ((ideal t : ENNReal) - good t)) ≤ badBound)
    (goodBound : ∀ t, (1 - error) * good t ≤ real t) (event : Set Transcript) :
    |(real.toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤
      badBound + error.toReal := by
  have goodFinite (t : Transcript) : good t ≠ ⊤ := ne_top_of_le_ne_top (ideal.apply_ne_top t) (goodLe t)
  have missingFinite (t : Transcript) : ideal t - good t ≠ ⊤ :=
    ne_top_of_le_ne_top (ideal.apply_ne_top t) tsub_le_self
  have goodTotal : (∑' t, good t) ≤ 1 := by
    exact (ENNReal.tsum_le_tsum goodLe).trans_eq ideal.tsum_coe
  have missingTotal : (∑' (t : Transcript), (ideal t - good t)) ≤ 1 := by
    exact (ENNReal.tsum_le_tsum (fun t => tsub_le_self)).trans_eq ideal.tsum_coe
  have goodSummable : Summable (fun t => (good t).toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top goodTotal)
  have missingSummable : Summable (fun t => (ideal t - good t).toReal) :=
    ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top missingTotal)
  let loss := fun t => (ideal t - good t).toReal + error.toReal * (good t).toReal
  have lossSummable : Summable loss := missingSummable.add (goodSummable.mul_left error.toReal)
  have pointwise (t : Transcript) : (ideal t).toReal ≤ (real t).toReal + loss t := by
    have ratio := ENNReal.toReal_mono (real.apply_ne_top t) (goodBound t)
    rw [ENNReal.toReal_mul] at ratio
    have subtraction := ENNReal.le_toReal_sub (a := 1) errorFinite
    rw [ENNReal.toReal_one] at subtraction
    have weighted := mul_le_mul_of_nonneg_right subtraction (ENNReal.toReal_nonneg (a := good t))
    have missing := ENNReal.toReal_sub_of_le (goodLe t) (ideal.apply_ne_top t)
    dsimp only [loss]
    rw [missing]
    nlinarith
  have estimate := hCoefficient_event_of_errorMass real ideal loss
    (fun t => add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)) lossSummable pointwise event
  apply estimate.trans
  rw [show (∑' t, loss t) = (∑' t, (ideal t - good t).toReal) +
      error.toReal * ∑' t, (good t).toReal from by
    rw [Summable.tsum_add missingSummable (goodSummable.mul_left error.toReal), tsum_mul_left]]
  rw [← ENNReal.tsum_toReal_eq missingFinite, ← ENNReal.tsum_toReal_eq goodFinite]
  have totalReal := ENNReal.toReal_mono ENNReal.one_ne_top goodTotal
  rw [ENNReal.toReal_one] at totalReal
  exact add_le_add missingBound
    ((mul_le_mul_of_nonneg_left totalReal ENNReal.toReal_nonneg).trans_eq (mul_one _))


/-- The source bad event and the retained source ratio bound every transcript event. -/
theorem hCoefficient_event_of_sourceGoodMass {Source Transcript : Type*}
    (real : PMF Transcript) (samples : PMF Source) (kernel : Source → PMF Transcript)
    (bad : Set Source) (error : ENNReal) (errorFinite : error ≠ ⊤)
    (badBound : ℝ) (badMass : (samples.toOuterMeasure bad).toReal ≤ badBound)
    (ratio : ∀ t, (1 - error) * sourceGoodMass samples kernel bad t ≤ real t)
    (event : Set Transcript) :
    |(real.toOuterMeasure event).toReal - ((samples.bind kernel).toOuterMeasure event).toReal| ≤
      badBound + error.toReal := by
  apply hCoefficient_event_of_goodSubmass real (samples.bind kernel)
    (sourceGoodMass samples kernel bad) error errorFinite badBound
    (sourceGoodMass_le samples kernel bad) _ ratio event
  rwa [sourceGoodMass_missing]

end

end Kriterion.ArgoMAC.Security
