import Proof.Shared.HCoefficient

namespace Kriterion.ArgoMAC.Security

noncomputable section
open scoped ENNReal

/-- This mass removes bad source coins and hides the source tag. -/
def sourceGoodMass {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source)
    (transcript : Transcript) : ℝ≥0∞ := by
  classical
  exact ∑' source, samples source * if source ∈ bad then 0 else kernel source transcript

/-- The good source mass is at most the full transcript mass. -/
theorem sourceGoodMass_le {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source)
    (transcript : Transcript) :
    sourceGoodMass samples kernel bad transcript ≤ (samples.bind kernel) transcript := by
  classical
  rw [sourceGoodMass, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro source
  by_cases member : source ∈ bad <;> simp [member]

/-- The good and bad source masses partition each transcript mass. -/
theorem sourceGoodMass_partition {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source)
    (transcript : Transcript) :
    sourceGoodMass samples kernel bad transcript + sourceGoodMass samples kernel badᶜ transcript =
      (samples.bind kernel) transcript := by
  classical
  rw [sourceGoodMass, sourceGoodMass, ← ENNReal.tsum_add, PMF.bind_apply]
  apply tsum_congr
  intro source
  by_cases member : source ∈ bad <;> simp [member]

/-- The total good source mass equals the probability of the good source event. -/
theorem sourceGoodMass_total {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source) :
    (∑' transcript, sourceGoodMass samples kernel bad transcript) =
      samples.toOuterMeasure badᶜ := by
  classical
  simp only [sourceGoodMass]
  rw [ENNReal.tsum_comm, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro source
  by_cases member : source ∈ bad
  · simp [member, Set.indicator]
  · simp only [member, ↓reduceIte, ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
    simp [member, Set.indicator]

/-- The missing transcript mass equals the probability of the bad source event. -/
theorem sourceGoodMass_missing {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source) :
    (∑' (transcript : Transcript), ((samples.bind kernel : PMF Transcript) transcript - sourceGoodMass samples kernel bad transcript : ℝ≥0∞)) =
      samples.toOuterMeasure bad := by
  have pointwise (transcript : Transcript) :
      (samples.bind kernel : PMF Transcript) transcript - sourceGoodMass samples kernel bad transcript =
        sourceGoodMass samples kernel badᶜ transcript := by
    rw [← sourceGoodMass_partition samples kernel bad transcript]
    exact ENNReal.add_sub_cancel_left
      (ne_top_of_le_ne_top ((samples.bind kernel).apply_ne_top transcript)
        (sourceGoodMass_le samples kernel bad transcript))
  simp_rw [pointwise]
  rw [sourceGoodMass_total, compl_compl]

end
end Kriterion.ArgoMAC.Security
