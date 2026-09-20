import Construction.Simulator.IntegerTrial
import Proof.Privacy.Simulator.Arithmetic.WideSampler
import Proof.Privacy.Simulator.BoundedIntegerSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
set_option exponentiation.threshold 257

/-- The trial program contains all twelve low-word sampling instructions. -/
theorem integerTrial_contains (width : Nat) (bound : Word) (full : Bool) :
    ContainsWordSampler (integerTrial width bound full) width trialLabels := by
  intro pc inside
  simp [integerTrial, trialLabels, inside]

/-- This observer returns a value only when the machine sets its acceptance flag. -/
def trialValue (memory : Memory) : Option Word :=
  if memory.registers 7 = 0 then none else some (memory.registers 0)

/-- This frame records the narrow comparison and its fixed bound. -/
def narrowTrialFrame (base : Memory) (value bound : Word) : Memory :=
  {wideFrame base value false with
    registers := Function.update (Function.update (wideFrame base value false).registers 5 bound)
      7 (if value.toNat < bound.toNat then 1 else 0)}

/-- The narrow comparison takes four instructions after the sampled word. -/
theorem integerTrial_narrow_tail [BN254.FieldCertificate]
    (width : Nat) (base : Memory) (value bound : Word) :
    run (integerTrial width bound false) 4 ⟨12, frame base value 0 0⟩ =
      PMF.pure (some (⟨19, narrowTrialFrame base value bound⟩, 4)) := by
  simp [run, step, integerTrial, frame, wideFrame, narrowTrialFrame, Arithmetic.eval,
    PMF.pure_map, Function.update_comm]
  rfl

/-- The narrow trial charges every draw and comparison instruction. -/
theorem integerTrial_narrow_run [BN254.FieldCertificate]
    (width : Nat) (base : Memory) (bound : Word) (fits : width ≤ 256) :
    run (integerTrial width bound false) (7 * width + 9) ⟨0, base⟩ =
      (coinFold width 0).map fun value =>
        some (⟨19, narrowTrialFrame base value bound⟩, 7 * width + 9) := by
  rw [show 7 * width + 9 = (7 * width + 5) + 4 by omega, run_after_prefix]
  change (runPrefix (integerTrial width bound false) (7 * width + 5)
    ⟨trialLabels 0, base⟩).bind _ = _
  erw [wordBlock_prefix (integerTrial width bound false) width trialLabels
    (integerTrial_contains width bound false) base fits]
  simp only [PMF.bind_map, Function.comp_def]
  change (coinFold width 0).bind (fun value =>
    (run (integerTrial width bound false) 4 ⟨12, frame base value 0 0⟩).map _) = _
  change (coinFold width 0).bind _ = (coinFold width 0).bind _
  congr 1
  funext value
  erw [integerTrial_narrow_tail]
  simp [PMF.pure_map, Nat.add_comm]

/-- The machine flag agrees with the integer comparison. -/
theorem trialValue_narrow (base : Memory) (value bound : Word) :
    trialValue (narrowTrialFrame base value bound) =
      if value.toNat < bound.toNat then some value else none := by
  by_cases accepted : value.toNat < bound.toNat <;>
    simp [trialValue, narrowTrialFrame, wideFrame, frame, accepted]

/-- The narrow trial returns the exact accepted-word law and its actual cost. -/
theorem integerTrial_narrow_law [BN254.FieldCertificate]
    (width : Nat) (base : Memory) (bound : Word) (fits : width ≤ 256) :
    (run (integerTrial width bound false) (7 * width + 9) ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (coinFold width 0).map fun value =>
          some ((if value.toNat < bound.toNat then some value else none), 7 * width + 9) := by
  rw [integerTrial_narrow_run width base bound fits, PMF.map_comp]
  simp only [Function.comp_def, Option.map_some, trialValue_narrow]

/-- The machine trial matches the source trial for every range with at most 256 sampled bits. -/
theorem integerTrial_source_narrow [BN254.FieldCertificate] (size : Nat) (base : Memory)
    (fits : Security.BoundedIntegerSampling.width size ≤ 256) :
    (run (integerTrial (Security.BoundedIntegerSampling.width size) (BitVec.ofNat 256 size) false)
      (7 * Security.BoundedIntegerSampling.width size + 9) ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (Security.BoundedIntegerSampling.trial size).map fun value =>
          some (value.map (fun accepted => BitVec.ofNat 256 accepted.val),
            7 * Security.BoundedIntegerSampling.width size + 9) := by
  have blockBound : Security.BoundedIntegerSampling.blockSize size ≤ 2 ^ 256 :=
    Nat.pow_le_pow_right (by decide) fits
  have sizeBound : size < 2 ^ 256 :=
    lt_of_lt_of_le (Security.BoundedIntegerSampling.size_lt_blockSize size) blockBound
  rw [integerTrial_narrow_law _ base _ fits, coinFold_uniform]
  simp only [zero_mul, zero_add, PMF.map_comp, Security.BoundedIntegerSampling.trial]
  congr 1
  funext block
  have within : block.val < 2 ^ 256 := lt_of_lt_of_le block.isLt blockBound
  simp only [Function.comp_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt within,
    Nat.mod_eq_of_lt sizeBound, Security.BoundedIntegerSampling.accept]
  split <;> rfl

/-- This frame rejects the draw exactly when the high bit is one. -/
def fullTrialFrame (base : Memory) (value : Word) (bit : Bool) : Memory :=
  {wideFrame base value bit with
    registers := Function.update (wideFrame base value bit).registers 7 (if bit then 0 else 1)}

/-- The full-range comparison takes five instructions after the low word. -/
theorem integerTrial_full_tail [BN254.FieldCertificate]
    (width : Nat) (base : Memory) (value bound : Word) :
    run (integerTrial width bound true) 5 ⟨12, frame base value 0 0⟩ =
      (PMF.uniformOfFintype Bool).map fun bit =>
        some (⟨19, fullTrialFrame base value bit⟩, 5) := by
  simp [run, step, integerTrial, frame, Function.update, PMF.map_bind, PMF.bind_bind]
  congr 1
  funext bit
  cases bit <;> simp [PMF.pure_map, Arithmetic.eval, fullTrialFrame, wideFrame, frame,
    Function.update_comm] <;> rfl

/-- The full-range trial charges its extra bit and comparison. -/
theorem integerTrial_full_run [BN254.FieldCertificate] (base : Memory) (bound : Word) :
    run (integerTrial 256 bound true) 1802 ⟨0, base⟩ =
      (PMF.uniformOfFintype Word).bind fun value =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          some (⟨19, fullTrialFrame base value bit⟩, 1802) := by
  rw [show 1802 = (7 * 256 + 5) + 5 from rfl, run_after_prefix]
  change (runPrefix (integerTrial 256 bound true) (7 * 256 + 5)
    ⟨trialLabels 0, base⟩).bind _ = _
  erw [wordBlock_prefix (integerTrial 256 bound true) 256 trialLabels
    (integerTrial_contains 256 bound true) base (by decide)]
  rw [coinFold_word_uniform]
  simp only [PMF.bind_map, Function.comp_def]
  congr 1
  funext value
  change (run (integerTrial 256 bound true) 5 ⟨12, frame base value 0 0⟩).map _ = _
  erw [integerTrial_full_tail]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some]

/-- The full-range flag agrees with rejection of the high bit. -/
theorem trialValue_full (base : Memory) (value : Word) (bit : Bool) :
    trialValue (fullTrialFrame base value bit) = if bit then none else some value := by
  cases bit <;> simp [trialValue, fullTrialFrame, wideFrame, frame]

/-- The full-range trial retains all low bits and rejects one half of its draws. -/
theorem integerTrial_full_law [BN254.FieldCertificate] (base : Memory) (bound : Word) :
    (run (integerTrial 256 bound true) 1802 ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (PMF.uniformOfFintype Word).bind fun value =>
          (PMF.uniformOfFintype Bool).map fun bit =>
            some ((if bit then none else some value), 1802) := by
  rw [integerTrial_full_run, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, Option.map_some, trialValue_full]

/-- The full-range machine trial matches the source trial, including rejected draws. -/
theorem integerTrial_source_full [BN254.FieldCertificate] (base : Memory) :
    (run (integerTrial 256 0 true) 1802 ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (Security.BoundedIntegerSampling.trial (2 ^ 256)).map fun value =>
          some (value.map (fun accepted => BitVec.ofNat 256 accepted.val), 1802) := by
  rw [integerTrial_full_law]
  change ((PMF.uniformOfFintype Word).bind fun value =>
    (PMF.uniformOfFintype Bool).bind fun bit =>
      PMF.pure (some ((if bit then none else some value), 1802))) = _
  rw [← Security.uniform_product_bind (fun pair : Word × Bool =>
    PMF.pure (some ((if pair.2 then none else some pair.1), 1802)))]
  unfold Security.BoundedIntegerSampling.trial
  change (PMF.uniformOfFintype (Word × Bool)).map _ =
    ((PMF.uniformOfFintype (Fin (2 ^ 257))).map
      (fun sample => if inside : sample.val < 2 ^ 256 then
        some (⟨sample.val, inside⟩ : Fin (2 ^ 256)) else none)).map _
  rw [← Security.uniform_map_equiv widePair]
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext pair
  rcases pair with ⟨value, bit⟩
  simp only [Function.comp_def, widePair_value]
  cases bit
  · simp [value.isLt]
  · simp

/-- This count includes the draw, the comparison, and the halt. -/
def trialCost (size : Nat) : Nat :=
  if size = 2 ^ 256 then 1802 else 7 * (size.log2 + 1) + 9

/-- A strict subrange needs at most 256 sampled bits. -/
theorem narrowWidth (size : Nat) (positive : 0 < size) (small : size < 2 ^ 256) :
    Security.BoundedIntegerSampling.width size ≤ 256 := by
  have power : 2 ^ size.log2 < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.log2_self_le (Nat.ne_of_gt positive)) small
  have logarithm := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp power
  unfold Security.BoundedIntegerSampling.width
  omega

/-- The closed trial matches the source law for every supported nonempty range. -/
theorem boundedTrial_source [BN254.FieldCertificate] (size : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (run (boundedTrial size) (trialCost size) ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (Security.BoundedIntegerSampling.trial size).map fun value =>
          some (value.map (fun accepted => BitVec.ofNat 256 accepted.val), trialCost size) := by
  by_cases full : size = 2 ^ 256
  · subst size
    have selected : boundedTrial (2 ^ 256) = integerTrial 256 0 true := by
      simp only [boundedTrial, Nat.log2_two_pow]
      rfl
    rw [selected]
    simpa [trialCost] using integerTrial_source_full base
  · have fits := narrowWidth size positive (lt_of_le_of_ne bounded full)
    have selected : boundedTrial size =
        integerTrial (Security.BoundedIntegerSampling.width size) (BitVec.ofNat 256 size) false := by
      simp only [boundedTrial, beq_eq_false_iff_ne.mpr full,
        Security.BoundedIntegerSampling.width]
      change size.log2 + 1 ≤ 256 at fits
      rw [Nat.min_eq_left fits]
    rw [selected]
    simpa only [trialCost, if_neg full, Security.BoundedIntegerSampling.width] using
      integerTrial_source_narrow size base fits

/-- Each trial uses at most 1802 instructions and a 20-entry program table. -/
theorem boundedTrial_cost (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    trialCost size ≤ 1802 ∧ (boundedTrial size).size + 1 = 20 := by
  constructor
  · by_cases full : size = 2 ^ 256
    · simp [trialCost, full]
    · have fits := narrowWidth size positive (lt_of_le_of_ne bounded full)
      unfold Security.BoundedIntegerSampling.width at fits
      simp only [trialCost, if_neg full]
      omega
  · rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
