import Construction.Simulator.PolynomialInput
import Proof.Privacy.Simulator.Arithmetic.GatePolynomial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine

/-- The input loader supplies all four exact polynomial factors. -/
theorem polynomialInputProgram_values (base : Memory) (input : AffineInput)
    (coordinates : base.ram (base.registers 11) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 11 + 1) = BitVec.ofNat 256 input.y.val) :
    ∀ factor, (executeLinear polynomialInputProgram base).registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val := by
  have yword : base.ram (base.registers 11 + 1#256) = BitVec.ofNat 256 input.y.val := coordinates.2
  intro factor
  fin_cases factor <;>
    simp [polynomialInputProgram, polynomialInput, polynomialFactorRegister, executeLinear,
      LinearInstruction.execute, show Arithmetic.add.eval = (· + ·) from rfl, coordinates,
      yword, fieldMul_words, pow_two]

/-- The input loader preserves all source data and caller registers. -/
theorem polynomialInputProgram_preserves (base : Memory) :
    (executeLinear polynomialInputProgram base).ram = base.ram ∧
    (executeLinear polynomialInputProgram base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val →
      (executeLinear polynomialInputProgram base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [polynomialInputProgram, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 7 (by decide)),
    Function.update_of_ne (different 8 (by decide))]

/-- The input loader charges six fixed instructions. -/
theorem polynomialInputProgram_length : polynomialInputProgram.length = 6 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
