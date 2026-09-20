import Proof.Privacy.Simulator.Arithmetic.RuntimeTrial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every runtime-trial instruction before its return. -/
def ContainsRuntimeTrial (host : Machine) (labels : Fin 27 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 27, pc.val < 26 → host.code[(labels pc).val] =
    relocate labels (runtimeTrial.code[pc.val]'(by exact pc.isLt))

/-- The host contains the runtime width routine. -/
theorem runtimeTrialBlock_width (host : Machine) (labels : Fin 27 → Fin (host.size + 1))
    (present : ContainsRuntimeTrial host labels) :
    ContainsRangeWidth host (labels ∘ runtimeWidthLabels) := by
  intro pc inside
  have selected := present (runtimeWidthLabels pc) (by change pc.val < 26; omega)
  have source := runtimeTrial_width pc inside
  exact (selected.trans (congrArg (relocate labels) source)).trans
    (relocate_comp runtimeWidthLabels labels _)

/-- The host contains the runtime word loop. -/
theorem runtimeTrialBlock_word (host : Machine) (labels : Fin 27 → Fin (host.size + 1))
    (present : ContainsRuntimeTrial host labels) :
    ContainsWordLoop host (labels ∘ runtimeWordLabels) := by
  intro pc lower upper
  have selected := present (runtimeWordLabels pc) (by change pc.val + 6 < 26; omega)
  have source := runtimeTrial_word pc lower upper
  exact (selected.trans (congrArg (relocate labels) source)).trans
    (relocate_comp runtimeWordLabels labels _)

/-- The full-range tail returns after five instructions. -/
theorem runtimeTrialBlock_full_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsRuntimeTrial host labels)
    (base : Memory) (value : Word) (zero : base.registers 5 = 0#256) :
    runPrefix host 5 ⟨labels 18, frame base value 0 0⟩ =
      (PMF.uniformOfFintype Bool).map fun bit =>
        some (false, ⟨labels 26, fullTrialFrame base value bit⟩, 5) := by
  simp [runPrefix, step, present 18 (by decide), present 19 (by decide), present 20 (by decide),
    present 21 (by decide), present 22 (by decide), present 24 (by decide), runtimeTrial,
    relocate, frame, Function.update, zero, PMF.map_bind, PMF.bind_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype Bool))
  funext bit
  cases bit <;> simp [present 21 (by decide), present 22 (by decide), present 24 (by decide),
    runtimeTrial, relocate, PMF.pure_map, Arithmetic.eval, fullTrialFrame, wideFrame, frame,
    Function.update_comm] <;> rfl

/-- The ordinary tail returns after three instructions. -/
theorem runtimeTrialBlock_narrow_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsRuntimeTrial host labels)
    (base : Memory) (value : Word) (nonzero : base.registers 5 ≠ 0#256) :
    runPrefix host 3 ⟨labels 18, frame base value 0 0⟩ =
      PMF.pure (some (false, ⟨labels 26, narrowTrialFrame base value (base.registers 5)⟩, 3)) := by
  have same : Function.update (wideFrame base value false).registers 5 (base.registers 5) =
      (wideFrame base value false).registers := by
    have atFive : (wideFrame base value false).registers 5 = base.registers 5 := by
      simp [wideFrame, frame]
    rw [← atFive, Function.update_eq_self]
  simp only [narrowTrialFrame, same]
  simp [runPrefix, step, present 18 (by decide), present 23 (by decide), present 25 (by decide),
    runtimeTrial, relocate, frame, wideFrame, Arithmetic.eval, nonzero, PMF.pure_map,
    Function.update_comm]


/-- The runtime trial has a positive instruction cost. -/
theorem runtimeTrialCost_positive (bound : Word) : 1 ≤ runtimeTrialCost bound := by
  unfold runtimeTrialCost
  split <;> omega

/-- The embedded trial passes its sampled word to the comparison branch. -/
theorem runtimeTrialBlock_sample [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsRuntimeTrial host labels)
    (base : Memory) :
    runPrefix host (runtimeTrialCost (base.registers 5) - 1) ⟨labels 0, base⟩ =
      (coinFold (lowWidth (base.registers 5)) 0).bind fun value =>
        (runPrefix host (if base.registers 5 = 0#256 then 5 else 3)
          ⟨labels 18, frame base value 0 0⟩).map
          (Option.map fun result => (result.1, result.2.1,
            result.2.2 + (7 * lowWidth (base.registers 5) + 2) + widthCost (base.registers 5))) := by
  let bits := lowWidth (base.registers 5)
  let tailCost := if base.registers 5 = 0#256 then 5 else 3
  have width := widthBlock_run host (labels ∘ runtimeWidthLabels)
    (runtimeTrialBlock_width host labels present) base
  have continued := prefix_add host (widthCost (base.registers 5))
    (7 * bits + 2 + tailCost) ⟨(labels ∘ runtimeWidthLabels) 0, base⟩
  rw [width] at continued
  have total : runtimeTrialCost (base.registers 5) - 1 =
      widthCost (base.registers 5) + (7 * bits + 2 + tailCost) := by
    dsimp [runtimeTrialCost, bits, tailCost]
    split <;> omega
  rw [total]
  change runPrefix host (widthCost (base.registers 5) + (7 * bits + 2 + tailCost))
    ⟨(labels ∘ runtimeWidthLabels) 0, base⟩ = _
  rw [continued, PMF.pure_bind]
  change (runPrefix host (7 * bits + 2 + tailCost)
    ⟨(labels ∘ runtimeWordLabels) 3, frame base 0 bits 0⟩).map _ = _
  have sample := wordBlock_loop host bits (labels ∘ runtimeWordLabels)
    (runtimeTrialBlock_word host labels present) base 0 0 (lowWidth_bound (base.registers 5))
  have sampled := prefix_add host (7 * bits + 2) tailCost
    ⟨(labels ∘ runtimeWordLabels) 3, frame base 0 bits 0⟩
  rw [sample] at sampled
  rw [sampled]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.map_comp]
  apply congrArg (PMF.bind (coinFold bits 0))
  funext value
  change (runPrefix host tailCost ⟨labels 18, frame base value 0 0⟩).map _ = _
  apply congrArg (fun f => PMF.map f (runPrefix host tailCost ⟨labels 18, frame base value 0 0⟩))
  funext result
  cases result <;> rfl

/-- The embedded runtime trial retains its complete memory law. -/
theorem runtimeTrialBlock_run [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsRuntimeTrial host labels)
    (base : Memory) :
    runPrefix host (runtimeTrialCost (base.registers 5) - 1) ⟨labels 0, base⟩ =
      (trialMemory (runtimeRange (base.registers 5)) base).map fun memory =>
        some (false, ⟨labels 26, memory⟩, runtimeTrialCost (base.registers 5) - 1) := by
  rw [runtimeTrialBlock_sample host labels present]
  by_cases zero : base.registers 5 = 0#256
  · simp only [lowWidth, runtimeRange, if_pos zero, trialMemory, ite_true,
      PMF.map_bind, PMF.map_comp, Function.comp_def, coinFold_word_uniform]
    apply congrArg (PMF.bind (PMF.uniformOfFintype Word))
    funext value
    rw [runtimeTrialBlock_full_tail host labels present base value zero]
    simp only [PMF.map_comp, Function.comp_def, Option.map_some, runtimeTrialCost, lowWidth,
      widthCost, if_pos zero]
  · have positive := word_positive (base.registers 5) zero
    have below : (base.registers 5).toNat ≠ 2 ^ 256 := Nat.ne_of_lt (base.registers 5).isLt
    simp only [trialMemory, lowWidth, if_neg zero, runtimeRange, if_neg below,
      bitLength, if_neg (Nat.ne_of_gt positive), Function.comp_def, PMF.map]
    have same : BitVec.ofNat 256 (base.registers 5).toNat = base.registers 5 := by simp
    rw [same]
    simp only [PMF.bind_bind, PMF.pure_bind]
    apply congrArg (PMF.bind (coinFold ((base.registers 5).toNat.log2 + 1) 0))
    funext value
    rw [runtimeTrialBlock_narrow_tail host labels present base value zero]
    simp only [PMF.pure_bind, Option.map_some, runtimeTrialCost, lowWidth, if_neg zero,
      bitLength, if_neg (Nat.ne_of_gt positive)]
    have arithmetic : 3 + (7 * ((base.registers 5).toNat.log2 + 1) + 2) +
        widthCost (base.registers 5) =
        widthCost (base.registers 5) + (7 * ((base.registers 5).toNat.log2 + 1) + 2) + 4 - 1 := by omega
    rw [arithmetic]

end Kriterion.ArgoMAC.ArithmeticSimulator
