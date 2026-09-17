import Proof.Shared.SourceGoodMass
namespace Kriterion.ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The complete tag fibers partition one normalized event. -/
theorem tagFiberMass_sum {A Tag : Type*} (samples : PMF A) (tag : A → Tag) (event : A → Prop) :
    (∑' value : Tag, samples.toOuterMeasure {a | tag a = value ∧ event a}) =
      samples.toOuterMeasure {a | event a} := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (tag a)]
  · by_cases member : event a <;> simp [Set.indicator, member]
  · intro value different
    simp [Ne.symm different]

/-- A retained tag sum is exactly the event with its tag restriction. -/
theorem tagFiberMass_restricted {A Tag : Type*} (samples : PMF A) (tag : A → Tag)
    (event : A → Prop) (kept : Tag → Prop) :
    (∑' value : Tag, if kept value then samples.toOuterMeasure {a | tag a = value ∧ event a} else 0) =
      samples.toOuterMeasure {a | event a ∧ kept (tag a)} := by
  classical
  rw [← tagFiberMass_sum samples tag (fun a => event a ∧ kept (tag a))]
  apply tsum_congr
  intro value
  by_cases retain : kept value
  · rw [if_pos retain]
    congr 1
    ext a
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨same, member⟩
      exact ⟨same, member, same.symm ▸ retain⟩
    · exact fun member => ⟨member.1, member.2.1⟩
  · rw [if_neg retain]
    have empty : {a | tag a = value ∧ event a ∧ kept (tag a)} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨same, _, member⟩
      exact retain (same ▸ member)
    rw [empty]
    simp

/-- Any retained tag sum is at most the whole normalized event. -/
theorem tagFiberMass_restricted_le {A Tag : Type*} (samples : PMF A) (tag : A → Tag)
    (event : A → Prop) (kept : Tag → Prop) :
    (∑' value : Tag, if kept value then samples.toOuterMeasure {a | tag a = value ∧ event a} else 0) ≤
      samples.toOuterMeasure {a | event a} := by
  classical
  rw [tagFiberMass_restricted samples tag event kept]
  exact MeasureTheory.measure_mono (fun _ member => member.1)

end
end Kriterion.ArgoMAC.Security
