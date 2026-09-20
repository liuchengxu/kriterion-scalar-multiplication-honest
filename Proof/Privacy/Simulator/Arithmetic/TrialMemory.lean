import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This law retains the memory after one complete trial. -/
noncomputable def trialMemory (size : Nat) (base : Memory) : PMF Memory :=
  if size = 2 ^ 256 then
    (PMF.uniformOfFintype Word).bind fun value =>
      (PMF.uniformOfFintype Bool).map (fullTrialFrame base value)
  else (coinFold (size.log2 + 1) 0).map fun value =>
    narrowTrialFrame base value (BitVec.ofNat 256 size)

/-- The full-word range selects the extra-bit trial. -/
theorem boundedTrial_full : boundedTrial (2 ^ 256) = integerTrial 256 0 true := by
  simp only [boundedTrial, Nat.log2_two_pow]
  rfl

/-- A strict subrange selects the ordinary comparison. -/
theorem boundedTrial_narrow (size : Nat) (different : size ≠ 2 ^ 256)
    (fits : size.log2 + 1 ≤ 256) :
    boundedTrial size = integerTrial (size.log2 + 1) (BitVec.ofNat 256 size) false := by
  simp only [boundedTrial, beq_eq_false_iff_ne.mpr different, Nat.min_eq_left fits]

/-- The machine retains the complete trial memory and its actual instruction cost. -/
theorem boundedTrial_memory [BN254.FieldCertificate] (size : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    run (boundedTrial size) (trialCost size) ⟨0, base⟩ =
      (trialMemory size base).map fun memory => some (⟨19, memory⟩, trialCost size) := by
  by_cases full : size = 2 ^ 256
  · subst size
    rw [boundedTrial_full]
    simp only [trialMemory, trialCost, if_pos rfl, ite_true, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact integerTrial_full_run base 0
  · have fits := narrowWidth size positive (lt_of_le_of_ne bounded full)
    rw [boundedTrial_narrow size full fits]
    simp only [trialMemory, trialCost, if_neg full, PMF.map_comp, Function.comp_def]
    exact integerTrial_narrow_run (size.log2 + 1) base (BitVec.ofNat 256 size) fits

/-- The trial memory gives the exact source acceptance law. -/
theorem trialMemory_source [BN254.FieldCertificate] (size : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (trialMemory size base).map trialValue =
      (Security.BoundedIntegerSampling.trial size).map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  have source := boundedTrial_source size base positive bounded
  rw [boundedTrial_memory size base positive bounded] at source
  have projected := congrArg
    (PMF.map (fun result : Option (Option Word × Nat) => result.bind Prod.fst)) source
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some] using projected

/-- Each trial preserves the retry counter and restores the constant-one register. -/
theorem trialMemory_registers (size : Nat) (base memory : Memory)
    (supported : memory ∈ (trialMemory size base).support) :
    memory.registers 4 = base.registers 4 ∧ memory.registers 1 = 1 := by
  unfold trialMemory at supported
  split at supported
  · obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨bit, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    simp [fullTrialFrame, wideFrame, frame]
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    simp [narrowTrialFrame, wideFrame, frame]

/-- The embedded trial retains the same memory law and returns before the halt. -/
theorem boundedTrial_block [BN254.FieldCertificate] (host : Machine) (size : Nat)
    (labels : Fin 20 → Fin (host.size + 1))
    (present : ContainsTrial host (min (size.log2 + 1) 256)
      (BitVec.ofNat 256 size) (size == 2 ^ 256) labels)
    (base : Memory) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    runPrefix host (trialCost size - 1) ⟨labels 0, base⟩ =
      (trialMemory size base).map fun memory =>
        some (false, ⟨labels 19, memory⟩, trialCost size - 1) := by
  by_cases full : size = 2 ^ 256
  · subst size
    have selected : ContainsTrial host 256 0 true labels := by
      have zero : BitVec.ofNat 256 (2 ^ 256) = 0 := by decide
      simpa only [Nat.log2_two_pow, zero, beq_self_eq_true,
        show min (256 + 1) 256 = 256 from rfl] using present
    simp only [trialCost, trialMemory, if_pos rfl, ite_true, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact trialBlock_full host 0 labels selected base
  · have fits := narrowWidth size positive (lt_of_le_of_ne bounded full)
    change size.log2 + 1 ≤ 256 at fits
    have selected : ContainsTrial host (size.log2 + 1) (BitVec.ofNat 256 size) false labels := by
      simpa only [Nat.min_eq_left fits, beq_eq_false_iff_ne.mpr full] using present
    simp only [trialCost, trialMemory, if_neg full, PMF.map_comp, Function.comp_def]
    have count : 7 * (size.log2 + 1) + 9 - 1 = 7 * (size.log2 + 1) + 8 := by omega
    rw [count]
    exact trialBlock_narrow host (size.log2 + 1) (BitVec.ofNat 256 size) labels selected base fits

end Kriterion.ArgoMAC.ArithmeticSimulator
