import Construction.Simulator.RuntimeTrial
import Proof.Privacy.Simulator.Arithmetic.RangeWidth
import Proof.Privacy.Simulator.Arithmetic.TrialMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The runtime trial contains the complete width routine. -/
theorem runtimeTrial_width : ContainsRangeWidth runtimeTrial runtimeWidthLabels := by
  intro pc inside
  simp [runtimeTrial, runtimeWidthLabels, inside]
  rfl

/-- The runtime trial contains the word loop without a fixed-width initialization. -/
theorem runtimeTrial_word : ContainsWordLoop runtimeTrial runtimeWordLabels := by
  intro pc lower upper
  have beyond : ¬pc.val + 6 < 9 := by omega
  have inside : pc.val + 6 < 18 := by omega
  simp [runtimeTrial, runtimeWordLabels, beyond, inside]

/-- The full-word comparison charges the range branch and the extra fair bit. -/
theorem runtimeTrial_full_tail [BN254.FieldCertificate] (base : Memory) (value : Word)
    (zero : base.registers 5 = 0#256) :
    run runtimeTrial 6 ⟨18, frame base value 0 0⟩ =
      (PMF.uniformOfFintype Bool).map fun bit =>
        some (⟨26, fullTrialFrame base value bit⟩, 6) := by
  simp [run, step, runtimeTrial, frame, Function.update, zero, PMF.map_bind, PMF.bind_bind]
  apply congrArg (PMF.bind (PMF.uniformOfFintype Bool))
  funext bit
  cases bit <;> simp [PMF.pure_map, Arithmetic.eval, fullTrialFrame, wideFrame, frame,
    Function.update_comm] <;> rfl

/-- The ordinary comparison reads the runtime bound directly. -/
theorem runtimeTrial_narrow_tail [BN254.FieldCertificate] (base : Memory) (value : Word)
    (nonzero : base.registers 5 ≠ 0#256) :
    run runtimeTrial 4 ⟨18, frame base value 0 0⟩ =
      PMF.pure (some (⟨26, narrowTrialFrame base value (base.registers 5)⟩, 4)) := by
  have same : Function.update (wideFrame base value false).registers 5 (base.registers 5) =
      (wideFrame base value false).registers := by
    have atFive : (wideFrame base value false).registers 5 = base.registers 5 := by
      simp [wideFrame, frame]
    rw [← atFive, Function.update_eq_self]
  simp only [narrowTrialFrame, same]
  simp [run, step, runtimeTrial, frame, wideFrame, Arithmetic.eval,
    nonzero, PMF.pure_map, Function.update_comm]
  rfl

/-- This count includes the width calculation, the sampled bits, the comparison, and the halt. -/
def runtimeTrialCost (bound : Word) : Nat :=
  widthCost bound + (7 * lowWidth bound + 2) + (if bound = 0#256 then 6 else 4)

/-- The runtime trial passes the sampled word to the correct comparison branch. -/
theorem runtimeTrial_sample [BN254.FieldCertificate] (base : Memory) :
    run runtimeTrial (runtimeTrialCost (base.registers 5)) ⟨0, base⟩ =
      (coinFold (lowWidth (base.registers 5)) 0).bind fun value =>
        (run runtimeTrial (if base.registers 5 = 0#256 then 6 else 4) ⟨18, frame base value 0 0⟩).map
          (Option.map fun result =>
            (result.1, result.2 + (7 * lowWidth (base.registers 5) + 2) + widthCost (base.registers 5))) := by
  let bits := lowWidth (base.registers 5)
  let tailCost := if base.registers 5 = 0#256 then 6 else 4
  have width := widthBlock_run runtimeTrial runtimeWidthLabels runtimeTrial_width base
  have continued := run_after_prefix runtimeTrial (widthCost (base.registers 5))
    (7 * bits + 2 + tailCost) ⟨runtimeWidthLabels 0, base⟩
  rw [width] at continued
  unfold runtimeTrialCost
  rw [Nat.add_assoc]
  change run runtimeTrial (widthCost (base.registers 5) + (7 * bits + 2 + tailCost))
    ⟨runtimeWidthLabels 0, base⟩ = _
  rw [continued, PMF.pure_bind]
  change (run runtimeTrial (7 * bits + 2 + tailCost)
    ⟨runtimeWordLabels 3, frame base 0 bits 0⟩).map _ = _
  have sample := wordBlock_loop runtimeTrial bits runtimeWordLabels runtimeTrial_word base 0 0
    (lowWidth_bound (base.registers 5))
  have sampled := run_after_prefix runtimeTrial (7 * bits + 2) tailCost
    ⟨runtimeWordLabels 3, frame base 0 bits 0⟩
  rw [sample] at sampled
  rw [sampled]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.map_comp]
  apply congrArg (PMF.bind (coinFold bits 0))
  funext value
  change (run runtimeTrial tailCost ⟨18, frame base value 0 0⟩).map _ = _
  apply congrArg (fun f => PMF.map f (run runtimeTrial tailCost ⟨18, frame base value 0 0⟩))
  funext result
  cases result <;> rfl

/-- The runtime trial retains the same complete memory law as the source trial. -/
theorem runtimeTrial_run [BN254.FieldCertificate] (base : Memory) :
    run runtimeTrial (runtimeTrialCost (base.registers 5)) ⟨0, base⟩ =
      (trialMemory (runtimeRange (base.registers 5)) base).map fun memory =>
        some (⟨26, memory⟩, runtimeTrialCost (base.registers 5)) := by
  rw [runtimeTrial_sample]
  by_cases zero : base.registers 5 = 0#256
  · simp only [lowWidth, runtimeRange, if_pos zero, trialMemory, ite_true,
      PMF.map_bind, PMF.map_comp, Function.comp_def, coinFold_word_uniform]
    apply congrArg (PMF.bind (PMF.uniformOfFintype Word))
    funext value
    rw [runtimeTrial_full_tail base value zero]
    simp only [PMF.map_comp, Function.comp_def, Option.map_some, runtimeTrialCost, lowWidth,
      widthCost, if_pos zero]
  · have positive := word_positive (base.registers 5) zero
    have notFull : runtimeRange (base.registers 5) ≠ 2 ^ 256 := by
      intro full
      exact zero ((runtimeRange_full (base.registers 5)).mp full)
    have below : (base.registers 5).toNat ≠ 2 ^ 256 := Nat.ne_of_lt (base.registers 5).isLt
    simp only [trialMemory, if_neg notFull, lowWidth, if_neg zero, runtimeRange, if_neg below,
      bitLength, if_neg (Nat.ne_of_gt positive), PMF.map_comp, Function.comp_def, PMF.map]
    have same : BitVec.ofNat 256 (base.registers 5).toNat = base.registers 5 := by simp
    rw [same]
    simp only [PMF.bind_bind, PMF.pure_bind]
    change (coinFold ((base.registers 5).toNat.log2 + 1) 0).bind _ =
      (coinFold ((base.registers 5).toNat.log2 + 1) 0).bind _
    apply congrArg (PMF.bind (coinFold ((base.registers 5).toNat.log2 + 1) 0))
    funext value
    rw [runtimeTrial_narrow_tail base value zero]
    simp only [PMF.pure_bind, PMF.pure_map, Option.map_some, Function.comp_def, runtimeTrialCost, lowWidth,
      if_neg zero, bitLength, if_neg (Nat.ne_of_gt positive)]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The runtime trial gives the exact bounded-integer source law. -/
theorem runtimeTrial_source [BN254.FieldCertificate] (base : Memory) :
    (run runtimeTrial (runtimeTrialCost (base.registers 5)) ⟨0, base⟩).map
      (fun result => result.bind fun outcome => trialValue outcome.1.memory) =
      (Security.BoundedIntegerSampling.trial (runtimeRange (base.registers 5))).map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  rw [runtimeTrial_run]
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_some] using
    trialMemory_source (runtimeRange (base.registers 5)) base
      (runtimeRange_bounds _).1 (runtimeRange_bounds _).2

/-- Each runtime trial uses at most 2572 instructions. -/
theorem runtimeTrialCost_bound (bound : Word) : runtimeTrialCost bound ≤ 2572 := by
  have bits := lowWidth_bound bound
  by_cases zero : bound = 0#256
  · simp [runtimeTrialCost, widthCost, lowWidth, zero]
  · simp only [runtimeTrialCost, widthCost, lowWidth, if_neg zero] at *
    omega

/-- The program table and one trial use at most 2599 cost units. -/
theorem runtimeTrial_totalCost (bound : Word) :
    runtimeTrial.size + 1 + runtimeTrialCost bound ≤ 2599 := by
  have bound := runtimeTrialCost_bound bound
  change 26 + 1 + _ ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
