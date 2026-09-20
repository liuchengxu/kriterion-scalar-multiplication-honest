import Construction.Simulator.OutputTargets
import Proof.Privacy.Simulator.Arithmetic.PointHornerSource
import Proof.Privacy.Simulator.Arithmetic.ClampPoint
import Proof.Privacy.Simulator.Arithmetic.OutputTargetRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains every instruction before the final output-target return. -/
def ContainsOutputTargets (host : Machine) (labels : Fin 4289 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 4289, pc.val < 4288 → host.code[(labels pc).val] = relocate labels (outputTargetsMachine.code[pc.val])

/-- The complete machine contains its Horner block. -/
theorem outputTargetsCode_horner (host : Machine) (labels : Fin 4289 → Fin (host.size + 1))
    (present : ContainsOutputTargets host labels) :
    ContainsPointHorner host 90 (by decide) (labels ∘ targetHornerLabels) := by
  intro pc inside
  have bound : pc.val < 1985 := inside
  change host.code[(labels (targetHornerLabels pc)).val] = _
  rw [present (targetHornerLabels pc) (by simp [targetHornerLabels]; omega)]
  rw [show outputTargetsMachine.code[(targetHornerLabels pc).val] =
      relocate targetHornerLabels ((pointHornerMachine 90 (by decide)).code[pc.val]) from by
    simp only [outputTargetsMachine, Vector.getElem_ofFn, targetHornerLabels]
    rw [dif_pos bound]]
  exact relocate_comp _ _ _

/-- The complete machine contains its correction block. -/
theorem outputTargetsCode_clamp (host : Machine) (labels : Fin 4289 → Fin (host.size + 1))
    (present : ContainsOutputTargets host labels) : ContainsClampPoint host (labels ∘ targetClampLabels) := by
  intro pc inside
  have first : ¬ 1985 + pc.val < 1985 := by omega
  have next : 1985 + pc.val < 2011 := by change pc.val < 26 at inside; omega
  change host.code[(labels (targetClampLabels pc)).val] = _
  rw [present (targetClampLabels pc) (by simp [targetClampLabels]; omega)]
  simp only [outputTargetsMachine, Vector.getElem_ofFn, targetClampLabels, first, dite_false, next, dite_true,
    Nat.add_sub_cancel_left]
  exact relocate_comp _ _ _

/-- The complete machine contains its homogeneous-row block. -/
theorem outputTargetsCode_rows (host : Machine) (labels : Fin 4289 → Fin (host.size + 1))
    (present : ContainsOutputTargets host labels) : ContainsHomogeneousRows host 90 (by decide) (labels ∘ targetRowLabels) := by
  intro pc inside
  have first : ¬ 2012 + pc.val < 1985 := by omega
  have second : ¬ 2012 + pc.val < 2011 := by omega
  have third : ¬ 2012 + pc.val = 2011 := by omega
  have last : 2012 + pc.val < 4288 := by change pc.val < 2276 at inside; omega
  change host.code[(labels (targetRowLabels pc)).val] = _
  rw [present (targetRowLabels pc) (by simp [targetRowLabels]; omega)]
  rw [show outputTargetsMachine.code[(targetRowLabels pc).val] =
      relocate targetRowLabels ((homogeneousRows 90 (by decide)).code[pc.val]) from by
    simp only [outputTargetsMachine, Vector.getElem_ofFn, targetRowLabels]
    rw [dif_neg first, dif_neg second, dif_neg third, dif_pos last]
    simp only [Nat.add_sub_cancel_left]]
  exact relocate_comp _ _ _

/-- The scale-pointer instruction preserves every other machine component. -/
def targetScalePointer (base : Memory) : Memory :=
  { base with registers := Function.update base.registers 11 (base.registers 14 + base.registers 9) }

/-- The host charges the scale-pointer instruction. -/
theorem outputTargetsCode_pointer [BN254.FieldCertificate] (host : Machine) (labels : Fin 4289 → Fin (host.size + 1))
    (present : ContainsOutputTargets host labels) (fuel : Nat) (base : Memory) :
    run host (fuel + 1) ⟨labels 2011, base⟩ =
      (run host fuel ⟨labels 2012, targetScalePointer base⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  have code := present 2011 (by decide)
  simp [outputTargetsMachine] at code
  simp [run, step, code, relocate, targetScalePointer, Arithmetic.eval]

end Kriterion.ArgoMAC.ArithmeticSimulator
