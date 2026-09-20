import Construction.Simulator.FieldPolynomial
import Proof.Privacy.Simulator.Arithmetic.FieldFold

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A multiplication sequence uses one fixed instruction for each factor. -/
theorem polynomialFactors_length (factors : List (Fin 4)) : (polynomialFactors factors).length = factors.length := by
  simp [polynomialFactors]

/-- The factor sequence preserves RAM, stacks, and every register except its accumulator. -/
theorem polynomialFactors_preserves (factors : List (Fin 4)) (base : Memory) :
    (executeLinear (polynomialFactors factors) base).ram = base.ram ∧
    (executeLinear (polynomialFactors factors) base).bits = base.bits ∧
    ∀ register : Register, register ≠ 0 →
      (executeLinear (polynomialFactors factors) base).registers register = base.registers register := by
  induction factors generalizing base with
  | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons factor factors ih =>
      let next := (LinearInstruction.arithmetic .fieldMul 0 0 (polynomialFactorRegister factor)).execute base
      change (executeLinear (polynomialFactors factors) next).ram = _ ∧ _
      have saved := ih next
      exact ⟨saved.1, saved.2.1, fun register outside => (saved.2.2 register outside).trans (by
        simp [next, LinearInstruction.execute, outside])⟩

/-- The factor sequence computes the exact typed field product. -/
theorem polynomialFactors_value (factors : List (Fin 4)) (values : Fin 4 → BN254.BaseField)
    (base : Memory) (initial : BN254.BaseField)
    (accumulator : base.registers 0 = BitVec.ofNat 256 initial.val)
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (values factor).val) :
    (executeLinear (polynomialFactors factors) base).registers 0 =
      BitVec.ofNat 256 (factors.foldl (fun product factor => product * values factor) initial).val := by
  induction factors generalizing base initial with
  | nil => exact accumulator
  | cons factor factors ih =>
      let next := (LinearInstruction.arithmetic .fieldMul 0 0 (polynomialFactorRegister factor)).execute base
      change (executeLinear (polynomialFactors factors) next).registers 0 = _
      apply ih next (initial * values factor)
      · simp only [next, LinearInstruction.execute, Function.update_self, accumulator, encoded, fieldMul_words]
      · intro other
        have different : polynomialFactorRegister other ≠ 0 := by
          intro same; have value := congrArg Fin.val same; simp [polynomialFactorRegister] at value
        simpa only [next, LinearInstruction.execute, Function.update_of_ne different] using encoded other

end Kriterion.ArgoMAC.ArithmeticSimulator
