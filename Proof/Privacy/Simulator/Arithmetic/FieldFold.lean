import Proof.Privacy.Simulator.Arithmetic.FieldFoldBody
import Construction.ArgoMAC.DigitAdaptor

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The field fold charges initialization and every source word. -/
theorem fieldFold_length (count start : Nat) : (fieldFold count start).length = 5 * count + 2 := by
  simp [fieldFold, fieldFoldBody_length, Nat.add_comm]; omega

/-- The complete field fold preserves RAM, stacks, and caller registers. -/
theorem fieldFold_preserves (count start : Nat) (base : Memory) :
    (executeLinear (fieldFold count start) base).ram = base.ram ∧
    (executeLinear (fieldFold count start) base).bits = base.bits ∧
    ∀ register : Register, 4 ≤ register.val →
      (executeLinear (fieldFold count start) base).registers register = base.registers register := by
  rw [fieldFold, executeLinear_append]
  have saved := fieldFoldBody_preserves count start (executeLinear [.constant 0 0, .constant 3 2] base)
  refine ⟨saved.1, saved.2.1, ?_⟩
  intro register caller
  rw [saved.2.2 register (by omega)]
  have notZero : register ≠ 0 := by intro same; have value := congrArg Fin.val same; omega
  have notThree : register ≠ 3 := by intro same; have value := congrArg Fin.val same; omega
  simp [executeLinear, LinearInstruction.execute, notZero, notThree]

/-- The list fold equals the original field-bit source. -/
theorem fieldFold_list (count : Nat) (values : Fin count → BN254.BaseField) :
    (List.ofFn values).foldr (fun value acc => 2 * acc + value) 0 = DigitAdaptor.fromBits values := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.foldr_cons, DigitAdaptor.fromBits, Fin.foldr_succ, ih]
      rfl

/-- The fixed arithmetic program evaluates the exact original field-bit source. -/
theorem fieldFold_value (count start : Nat) (values : Fin count → BN254.BaseField) (base : Memory)
    (source : ∀ i : Fin count,
      base.ram (base.registers 10 + BitVec.ofNat 256 (start + i.val)) = BitVec.ofNat 256 (values i).val) :
    (executeLinear (fieldFold count start) base).registers 0 = BitVec.ofNat 256 (DigitAdaptor.fromBits values).val := by
  let initialized := executeLinear [.constant 0 0, .constant 3 2] base
  have ram : initialized.ram = base.ram := rfl
  have pointer : initialized.registers 10 = base.registers 10 := by simp [initialized, executeLinear, LinearInstruction.execute]
  have zero : initialized.registers 0 = 0 := by simp [initialized, executeLinear, LinearInstruction.execute]
  have two : initialized.registers 3 = BitVec.ofNat 256 (2 : BN254.BaseField).val := by
    simp [initialized, executeLinear, LinearInstruction.execute]
    rfl
  have stored (i : Nat) (inside : i < (List.ofFn values).length) :
      initialized.ram (initialized.registers 10 + BitVec.ofNat 256 (start + i)) =
        BitVec.ofNat 256 ((List.ofFn values)[i]).val := by
    rw [ram, pointer]
    simpa only [List.getElem_ofFn] using source ⟨i, by simpa using inside⟩
  have body := fieldFoldBody_value (List.ofFn values) start initialized zero two stored
  rw [List.length_ofFn, fieldFold_list] at body
  rw [fieldFold, executeLinear_append]
  exact body

end Kriterion.ArgoMAC.ArithmeticSimulator
