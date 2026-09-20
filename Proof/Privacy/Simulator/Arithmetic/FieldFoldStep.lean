import Construction.Simulator.FieldFold
import Proof.Privacy.Simulator.Arithmetic.HomogeneousPoint
import Proof.Privacy.Simulator.Arithmetic.HashOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The field-add instruction returns the canonical field sum. -/
theorem fieldAdd_words (left right : BN254.BaseField) :
    Arithmetic.fieldAdd.eval (BitVec.ofNat 256 left.val) (BitVec.ofNat 256 right.val) =
      BitVec.ofNat 256 (left + right).val := by
  simp only [Arithmetic.eval, baseField_word_value, ZMod.natCast_zmod_val]

/-- The field-subtract instruction returns the canonical field difference. -/
theorem fieldSub_words (left right : BN254.BaseField) :
    Arithmetic.fieldSub.eval (BitVec.ofNat 256 left.val) (BitVec.ofNat 256 right.val) =
      BitVec.ofNat 256 (left - right).val := by
  simp only [Arithmetic.eval, baseField_word_value, ZMod.natCast_zmod_val]

/-- Each field-fold step uses five fixed instructions. -/
theorem fieldFoldStep_length (index : Nat) : (fieldFoldStep index).length = 5 := rfl

/-- Each field-fold step preserves RAM, stacks, and all registers above two. -/
theorem fieldFoldStep_preserves (index : Nat) (base : Memory) :
    (executeLinear (fieldFoldStep index) base).ram = base.ram ∧
    (executeLinear (fieldFoldStep index) base).bits = base.bits ∧
    ∀ register : Register, 3 ≤ register.val →
      (executeLinear (fieldFoldStep index) base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 3) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [fieldFoldStep, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 2 (by decide))]

/-- Each field-fold step computes twice the accumulator plus its source word. -/
theorem fieldFoldStep_value (index : Nat) (base : Memory) (accumulator value : BN254.BaseField)
    (initial : base.registers 0 = BitVec.ofNat 256 accumulator.val)
    (two : base.registers 3 = BitVec.ofNat 256 (2 : BN254.BaseField).val)
    (source : base.ram (base.registers 10 + BitVec.ofNat 256 index) = BitVec.ofNat 256 value.val) :
    (executeLinear (fieldFoldStep index) base).registers 0 = BitVec.ofNat 256 (2 * accumulator + value).val := by
  simp only [fieldFoldStep, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute]
  simp only [Function.update_self, Function.update_of_ne (by decide : (3 : Register) ≠ 1),
    Function.update_of_ne (by decide : (3 : Register) ≠ 2),
    Function.update_of_ne (by decide : (0 : Register) ≠ 1),
    Function.update_of_ne (by decide : (0 : Register) ≠ 2),
    Function.update_of_ne (by decide : (10 : Register) ≠ 2),
    Function.update_of_ne (by decide : (1 : Register) ≠ 0)]
  change Arithmetic.fieldAdd.eval (Arithmetic.fieldMul.eval (base.registers 3) (base.registers 0))
    (base.ram (base.registers 10 + BitVec.ofNat 256 index)) = _
  rw [initial, two, source, fieldMul_words, fieldAdd_words]

end Kriterion.ArgoMAC.ArithmeticSimulator
