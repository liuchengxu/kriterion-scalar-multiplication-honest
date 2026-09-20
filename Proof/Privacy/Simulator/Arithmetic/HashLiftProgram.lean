import Proof.Privacy.Simulator.Arithmetic.HashLiftWords
import Proof.Privacy.Simulator.Arithmetic.HashOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography.BoundedMachine

/-- The full lift program returns the three exact source limbs. -/
theorem hashLiftProgram_values (base : Memory) (target : BaseField) (quotient : HashLiftQuotient)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (quotientWord : base.registers 1 = BitVec.ofNat 256 quotient.val) :
    (executeLinear hashLiftProgram base).registers 4 = BitVec.ofNat 256 (liftLowSum target.val quotient.val % 2 ^ 128) ∧
    (executeLinear hashLiftProgram base).registers 5 = BitVec.ofNat 256 (liftMiddleSum target.val quotient.val % 2 ^ 128) ∧
    (executeLinear hashLiftProgram base).registers 6 = BitVec.ofNat 256 (liftHigh target.val quotient.val) := by
  have targetFits : target.val < 2 ^ 256 := lt_trans target.val_lt (by decide : baseFieldModulus < 2 ^ 256)
  have quotientFits : quotient.val < 2 ^ 256 := lt_trans quotient.isLt (by decide : hashLiftQuotientCount < 2 ^ 256)
  have middle : (baseFieldModulus / 2 ^ 128) * (quotient.val % 2 ^ 128) +
      (baseFieldModulus % 2 ^ 128) * (quotient.val / 2 ^ 128) + target.val / 2 ^ 128 +
      liftLowSum target.val quotient.val / 2 ^ 128 = liftMiddleSum target.val quotient.val := by
    unfold liftMiddleSum
    omega
  have low : (baseFieldModulus % 2 ^ 128) * (quotient.val % 2 ^ 128) + target.val % 2 ^ 128 =
      liftLowSum target.val quotient.val := rfl
  simp only [hashLiftProgram, hashLiftSplit, hashLiftLow, hashLiftMiddle, hashLiftUpper,
    executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_apply, Fin.reduceEq, ↓reduceIte]
  simp only [targetWord, quotientWord, wordMask128_nat, wordShift128_nat _ targetFits,
    wordShift128_nat _ quotientFits, wordMul_nat, wordAdd_nat, low,
    wordShift128_nat _ (liftLowSum_bound target.val quotient.val), middle,
    wordShift128_nat _ (liftMiddleSum_bound target quotient), liftHigh]
  simp only [Nat.add_comm, true_and]

private theorem hashLiftSplit_preserves (base : Memory) :
    (executeLinear hashLiftSplit base).ram = base.ram ∧
    (executeLinear hashLiftSplit base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear hashLiftSplit base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [hashLiftSplit, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 0 (by decide)),
    Function.update_of_ne (different 1 (by decide)),
    Function.update_of_ne (different 2 (by decide)),
    Function.update_of_ne (different 3 (by decide)),
    Function.update_of_ne (different 4 (by decide)),
    Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)),
    Function.update_of_ne (different 7 (by decide))]


private theorem hashLiftLow_preserves (base : Memory) :
    (executeLinear hashLiftLow base).ram = base.ram ∧
    (executeLinear hashLiftLow base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear hashLiftLow base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [hashLiftLow, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 4 (by decide)),
    Function.update_of_ne (different 8 (by decide))]


private theorem hashLiftMiddle_preserves (base : Memory) :
    (executeLinear hashLiftMiddle base).ram = base.ram ∧
    (executeLinear hashLiftMiddle base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear hashLiftMiddle base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [hashLiftMiddle, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide))]


private theorem hashLiftUpper_preserves (base : Memory) :
    (executeLinear hashLiftUpper base).ram = base.ram ∧
    (executeLinear hashLiftUpper base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear hashLiftUpper base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [hashLiftUpper, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)),
    Function.update_of_ne (different 7 (by decide))]

/-- The full lift program preserves RAM, protocol stacks, and all caller registers. -/
theorem hashLiftProgram_preserves (base : Memory) :
    (executeLinear hashLiftProgram base).ram = base.ram ∧
    (executeLinear hashLiftProgram base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear hashLiftProgram base).registers register = base.registers register := by
  rw [hashLiftProgram, executeLinear_append, executeLinear_append, executeLinear_append]
  have first := hashLiftSplit_preserves base
  have second := hashLiftLow_preserves (executeLinear hashLiftSplit base)
  have third := hashLiftMiddle_preserves (executeLinear hashLiftLow (executeLinear hashLiftSplit base))
  have fourth := hashLiftUpper_preserves (executeLinear hashLiftMiddle (executeLinear hashLiftLow (executeLinear hashLiftSplit base)))
  exact ⟨fourth.1.trans (third.1.trans (second.1.trans first.1)),
    fourth.2.1.trans (third.2.1.trans (second.2.1.trans first.2.1)), fun register caller =>
      (fourth.2.2 register caller).trans ((third.2.2 register caller).trans
        ((second.2.2 register caller).trans (first.2.2 register caller)))⟩

/-- The complete lift program charges all 21 instructions. -/
theorem hashLiftProgram_length : hashLiftProgram.length = 21 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
