import Proof.Shared.SourceGoodMass
import Proof.Privacy.Source.HiddenHashSource

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A source bind preserves the exact good mass of each component. -/
theorem sourceGoodMass_bind {Outer Source Transcript : Type*}
    (samples : PMF Outer) (sources : Outer → PMF Source) (kernel : Source → PMF Transcript)
    (bad : Set Source) (transcript : Transcript) :
    sourceGoodMass (samples.bind sources) kernel bad transcript =
      ∑' outer, samples outer * sourceGoodMass (sources outer) kernel bad transcript := by
  simp only [sourceGoodMass, PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro outer
  apply tsum_congr
  intro source
  rw [mul_assoc]

/-- A source map preserves the exact good mass under its inverse bad event. -/
theorem sourceGoodMass_map {Source Target Transcript : Type*}
    (samples : PMF Source) (project : Source → Target) (kernel : Target → PMF Transcript)
    (bad : Set Target) (transcript : Transcript) :
    sourceGoodMass (samples.map project) kernel bad transcript =
      sourceGoodMass samples (fun source => kernel (project source)) (project ⁻¹' bad) transcript := by
  exact pmf_map_weighted_sum samples project
    (fun target => if target ∈ bad then 0 else kernel target transcript)

/-- The retained transcript removes the extra transcript sum from the ghost good mass. -/
theorem sourceGoodMass_ghost {Source Transcript Ghost : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (ghost : PMF Ghost)
    (bad : Set ((Source × Transcript) × Ghost)) (transcript : Transcript) :
    sourceGoodMass
      (samples.bind fun source => (kernel source).bind fun output =>
        ghost.map fun hidden => ((source, output), hidden))
      (fun coin => PMF.pure coin.1.2) bad transcript =
      ∑' source, samples source *
        ∑' hidden, ghost hidden * if ((source, transcript), hidden) ∈ bad then 0 else kernel source transcript := by
  simp only [sourceGoodMass_bind, sourceGoodMass_map]
  apply tsum_congr
  intro source
  apply congrArg (samples source * ·)
  rw [tsum_eq_single transcript]
  · simp only [sourceGoodMass, Set.mem_preimage, PMF.pure_apply_self]
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro hidden
    by_cases member : ((source, transcript), hidden) ∈ bad
    · simp [member]
    · simp [member, mul_comm]
  · intro output different
    simp [sourceGoodMass, PMF.pure_apply, Ne.symm different]

/-- A nested source experiment preserves its exact ghost good mass. -/
theorem sourceGoodMass_nested_ghost {Outer Inner Choice Source Transcript Ghost : Type*}
    (outer : PMF Outer) (inner : PMF Inner) (choices : Outer → Inner → PMF Choice)
    (project : Outer → Inner → Choice → Source) (kernel : Source → PMF Transcript)
    (ghost : PMF Ghost) (bad : ((Source × Transcript) × Ghost) → Prop) (transcript : Transcript) :
    sourceGoodMass
      (outer.bind fun first => inner.bind fun second =>
        (choices first second).bind fun choice => (kernel (project first second choice)).bind fun output =>
          ghost.map fun hidden => ((project first second choice, output), hidden))
      (fun coin => PMF.pure coin.1.2) {coin | bad coin} transcript =
      ∑' first, outer first * ∑' second, inner second * ∑' choice, choices first second choice *
        ∑' hidden, ghost hidden *
          if bad ((project first second choice, transcript), hidden) then 0
          else kernel (project first second choice) transcript := by
  rw [sourceGoodMass_bind]
  apply tsum_congr
  intro first
  apply congrArg (outer first * ·)
  rw [sourceGoodMass_bind]
  apply tsum_congr
  intro second
  apply congrArg (inner second * ·)
  have law := sourceGoodMass_ghost ((choices first second).map (project first second))
    kernel ghost {coin | bad coin} transcript
  simp only [PMF.bind_map, Function.comp_def] at law
  rw [law, pmf_map_weighted_sum]
  simp only [Set.mem_setOf_eq]

/-- A source equality and component equalities preserve the nested ghost weights. -/
theorem sourceGoodMass_nested_ghost_transport {Outer Inner Choice Source Transcript Ghost : Type*}
    (samples : PMF ((Source × Transcript) × Ghost))
    (outer : PMF Outer) (inner : PMF Inner) (components : Outer → Inner → PMF ((Source × Transcript) × Ghost))
    (choices : Outer → Inner → PMF Choice) (project : Outer → Inner → Choice → Source)
    (kernel : Source → PMF Transcript) (ghost : PMF Ghost)
    (bad : ((Source × Transcript) × Ghost) → Prop) (transcript : Transcript)
    (weight : Outer → Inner → Choice → Ghost → ℝ≥0∞)
    (shared : samples = outer.bind fun first => inner.bind (components first))
    (component : ∀ first second, components first second =
      (choices first second).bind fun choice => (kernel (project first second choice)).bind fun output =>
        ghost.map fun hidden => ((project first second choice, output), hidden))
    (weights : ∀ first second choice hidden, weight first second choice hidden =
      if bad ((project first second choice, transcript), hidden) then 0
      else kernel (project first second choice) transcript) :
    sourceGoodMass samples (fun coin => PMF.pure coin.1.2) {coin | bad coin} transcript =
      ∑' first, outer first * ∑' second, inner second * ∑' choice, choices first second choice *
        ∑' hidden, ghost hidden * weight first second choice hidden := by
  rw [shared]
  have componentsEq := funext fun first => funext (component first)
  rw [componentsEq]
  simp only [weights]
  exact sourceGoodMass_nested_ghost outer inner choices project kernel ghost bad transcript

end
end Kriterion.ArgoMAC.Security
