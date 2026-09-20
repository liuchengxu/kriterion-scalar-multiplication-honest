import Proof.Privacy.Simulator.Arithmetic.FieldFoldStep

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The field-fold body charges five instructions for each source word. -/
theorem fieldFoldBody_length (count start : Nat) : (fieldFoldBody count start).length = 5 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [fieldFoldBody, ih, fieldFoldStep_length]; omega

/-- The field-fold body preserves all source data and caller registers. -/
theorem fieldFoldBody_preserves (count start : Nat) (base : Memory) :
    (executeLinear (fieldFoldBody count start) base).ram = base.ram ∧
    (executeLinear (fieldFoldBody count start) base).bits = base.bits ∧
    ∀ register : Register, 3 ≤ register.val →
      (executeLinear (fieldFoldBody count start) base).registers register = base.registers register := by
  induction count generalizing start with
  | zero => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | succ count ih =>
      rw [fieldFoldBody, executeLinear_append]
      have prior := ih (start + 1)
      have step := fieldFoldStep_preserves start (executeLinear (fieldFoldBody count (start + 1)) base)
      exact ⟨step.1.trans prior.1, step.2.1.trans prior.2.1, fun register caller =>
        (step.2.2 register caller).trans (prior.2.2 register caller)⟩

/-- The field-fold body evaluates the exact binary field combination. -/
theorem fieldFoldBody_value (values : List BN254.BaseField) (start : Nat) (base : Memory)
    (zero : base.registers 0 = 0) (two : base.registers 3 = BitVec.ofNat 256 (2 : BN254.BaseField).val)
    (source : ∀ i, (inside : i < values.length) →
      base.ram (base.registers 10 + BitVec.ofNat 256 (start + i)) = BitVec.ofNat 256 (values[i]).val) :
    (executeLinear (fieldFoldBody values.length start) base).registers 0 =
      BitVec.ofNat 256 (values.foldr (fun value acc => 2 * acc + value) 0).val := by
  induction values generalizing start with
  | nil => simpa [fieldFoldBody, executeLinear] using zero
  | cons value values ih =>
      have tailSource (i : Nat) (inside : i < values.length) :
          base.ram (base.registers 10 + BitVec.ofNat 256 (start + 1 + i)) = BitVec.ofNat 256 (values[i]).val := by
        have read := source (i + 1) (by simpa using inside)
        change base.ram (base.registers 10 + BitVec.ofNat 256 (start + (i + 1))) =
          BitVec.ofNat 256 (values[i]).val at read
        simpa only [show start + (i + 1) = start + 1 + i by omega] using read
      have tail := ih (start + 1) tailSource
      have saved := fieldFoldBody_preserves values.length (start + 1) base
      rw [List.length_cons, fieldFoldBody, executeLinear_append, List.foldr_cons]
      apply fieldFoldStep_value start _ _ value tail ((saved.2.2 3 (by decide)).trans two)
      rw [saved.1, saved.2.2 10 (by decide)]
      have read := source 0 (by simp)
      change base.ram (base.registers 10 + BitVec.ofNat 256 (start + 0)) = BitVec.ofNat 256 value.val at read
      simpa only [Nat.add_zero] using read

end Kriterion.ArgoMAC.ArithmeticSimulator
