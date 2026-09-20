import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The scale phase occupies the first 3549 instruction slots. -/
def onlineScaleLabels (pc : Fin 3550) : Fin 8772 := ⟨pc.val, by have h := pc.isLt; omega⟩

/-- The point phase starts after the two pointer-change instructions. -/
def onlinePointLabels (pc : Fin 5221) : Fin 8772 := ⟨pc.val + 3551, by have h := pc.isLt; omega⟩

/-- The online sampler stores 91 scales and 90 points in one fixed arithmetic program. -/
def onlineCode (attempts : Nat) : Vector (Instruction 8772) 8772 :=
  Vector.ofFn (fun pc : Fin 8772 =>
    if scales : pc.val < 3549 then
      relocate onlineScaleLabels ((samplerBatch onlineScalePlan attempts (by decide)).code[pc.val]'(by change pc.val < 3550; omega))
    else if pc.val = 3549 then .constant 8 91 3550
    else if pc.val = 3550 then .arithmetic .add 10 10 8 3551
    else if points : pc.val < 8771 then relocate onlinePointLabels ((pointBatch 90 attempts (by decide)).code[pc.val - 3551]'(by
      change pc.val - 3551 < 5221
      have h := pc.isLt
      omega)) else .halt)

/-- The online machine keeps its fixed size separate from its instruction table. -/
def onlineSampling (attempts : Nat) : Machine := ⟨8771, onlineCode attempts, by decide⟩

/-- A host contains every online instruction before the final return. -/
def ContainsOnlineSampling (host : Machine) (attempts : Nat) (labels : Fin 8772 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 8772, pc.val < 8771 →
    host.code[(labels pc).val] = relocate labels ((onlineSampling attempts).code[pc.val])

/-- The host contains the full scale batch. -/
theorem onlineSamplingBlock_scales (host : Machine) (attempts : Nat) (labels : Fin 8772 → Fin (host.size + 1))
    (present : ContainsOnlineSampling host attempts labels) :
    ContainsSamplerBatch host onlineScalePlan attempts (by decide) (labels ∘ onlineScaleLabels) := by
  intro pc inside
  have position : (onlineScaleLabels pc).val < 8771 := by
    change pc.val < 8771
    change pc.val < 3549 at inside
    omega
  have source : (onlineSampling attempts).code[(onlineScaleLabels pc).val] =
      relocate onlineScaleLabels ((samplerBatch onlineScalePlan attempts (by decide)).code[pc.val]) := by
    simp [onlineSampling, onlineCode, onlineScaleLabels, inside]
  exact ((present (onlineScaleLabels pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp onlineScaleLabels labels _)

/-- The host contains the full point batch. -/
theorem onlineSamplingBlock_points (host : Machine) (attempts : Nat) (labels : Fin 8772 → Fin (host.size + 1))
    (present : ContainsOnlineSampling host attempts labels) :
    ContainsPointBatch host 90 attempts (by decide) (labels ∘ onlinePointLabels) := by
  intro pc inside
  have bound := pc.isLt
  have position : (onlinePointLabels pc).val < 8771 := by
    change pc.val + 3551 < 8771
    change pc.val < 5220 at inside
    omega
  have source : (onlineSampling attempts).code[(onlinePointLabels pc).val] =
      relocate onlinePointLabels ((pointBatch 90 attempts (by decide)).code[pc.val]) := by
    simp [onlineSampling, onlineCode, onlinePointLabels, show ¬pc.val + 3551 < 3549 by omega, show pc.val + 3551 < 8771 by change pc.val < 5220 at inside; omega]
    rfl
  exact ((present (onlinePointLabels pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp onlinePointLabels labels _)

/-- The host changes the point destination pointer in two charged instructions. -/
theorem onlineSamplingBlock_pointer [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 8772 → Fin (host.size + 1)) (present : ContainsOnlineSampling host attempts labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + 2) ⟨labels 3549, base⟩ =
      (run host fuel ⟨labels 3551, onlinePointInitial base⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  have first := present 3549 (by decide)
  have second := present 3550 (by decide)
  have sourceFirst : (onlineSampling attempts).code[3549]'(by change 3549 < 8772; decide) = .constant 8 91 3550 := by
    simp only [onlineSampling, onlineCode, Vector.getElem_ofFn]
    rfl
  have sourceSecond : (onlineSampling attempts).code[3550]'(by change 3550 < 8772; decide) = .arithmetic .add 10 10 8 3551 := by
    simp only [onlineSampling, onlineCode, Vector.getElem_ofFn]
    rfl
  change host.code[(labels 3549).val] = relocate labels ((onlineSampling attempts).code[3549]'(by change 3549 < 8772; decide)) at first
  change host.code[(labels 3550).val] = relocate labels ((onlineSampling attempts).code[3550]'(by change 3550 < 8772; decide)) at second
  rw [sourceFirst] at first
  rw [sourceSecond] at second
  change host.code[(labels 3549).val] = .constant 8 91 (labels 3550) at first
  change host.code[(labels 3550).val] = .arithmetic .add 10 10 8 (labels 3551) at second
  simp [run, step, first, second, relocate, Arithmetic.eval, onlinePointInitial,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
