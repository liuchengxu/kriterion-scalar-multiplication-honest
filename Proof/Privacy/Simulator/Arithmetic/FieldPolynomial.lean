import Proof.Privacy.Simulator.Arithmetic.PolynomialTerm

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A compiled polynomial body preserves RAM, stacks, and all caller registers. -/
theorem polynomialBody_preserves (terms : List PolynomialTerm) (base : Memory) :
    (executeLinear (terms.flatMap polynomialTerm) base).ram = base.ram ∧
    (executeLinear (terms.flatMap polynomialTerm) base).bits = base.bits ∧
    ∀ register : Register, 5 ≤ register.val →
      (executeLinear (terms.flatMap polynomialTerm) base).registers register = base.registers register := by
  induction terms generalizing base with
  | nil => exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons term terms ih =>
      rw [List.flatMap_cons, executeLinear_append]
      have step := polynomialTerm_preserves term base
      have tail := ih (executeLinear (polynomialTerm term) base)
      exact ⟨tail.1.trans step.1, tail.2.1.trans step.2.1, fun register caller =>
        (tail.2.2 register caller).trans (step.2.2 register caller)⟩

/-- A compiled polynomial body evaluates every fixed term. -/
theorem polynomialBody_value (terms : List PolynomialTerm) (values : Fin 4 → BN254.BaseField)
    (sourceValue : PolynomialTerm → BN254.BaseField) (base : Memory) (initial : BN254.BaseField)
    (sources : ∀ term ∈ terms, PolynomialSource term base.ram (base.registers 10) (sourceValue term))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (values factor).val)
    (accumulator : base.registers 4 = BitVec.ofNat 256 initial.val) :
    (executeLinear (terms.flatMap polynomialTerm) base).registers 4 = BitVec.ofNat 256
      (terms.foldl (fun (sum : BN254.BaseField) (term : PolynomialTerm) => sum + term.factors.foldl (fun product factor => product * values factor) (sourceValue term)) initial).val := by
  induction terms generalizing base initial with
  | nil => exact accumulator
  | cons term terms ih =>
      rw [List.flatMap_cons, executeLinear_append, List.foldl_cons]
      have saved := polynomialTerm_preserves term base
      apply ih (executeLinear (polynomialTerm term) base)
      · intro other member
        rw [saved.1, saved.2.2 10 (by decide)]
        exact sources other (List.mem_cons_of_mem term member)
      · intro factor
        rw [saved.2.2 (polynomialFactorRegister factor) (by change 5 ≤ 5 + factor.val; omega)]
        exact encoded factor
      · exact polynomialTerm_value term values base (sourceValue term) initial
          (sources term (List.mem_cons_self)) encoded accumulator

/-- The complete polynomial program preserves RAM, stacks, and caller registers. -/
theorem polynomial_preserves (terms : List PolynomialTerm) (base : Memory) :
    (executeLinear (polynomial terms) base).ram = base.ram ∧
    (executeLinear (polynomial terms) base).bits = base.bits ∧
    ∀ register : Register, 5 ≤ register.val →
      (executeLinear (polynomial terms) base).registers register = base.registers register := by
  rw [polynomial, executeLinear_append]
  have saved := polynomialBody_preserves terms (executeLinear [.constant 4 0] base)
  refine ⟨saved.1, saved.2.1, ?_⟩
  intro register caller
  rw [saved.2.2 register caller]
  have different : register ≠ 4 := by intro same; have value := congrArg Fin.val same; omega
  simp [executeLinear, LinearInstruction.execute, different]

/-- The complete polynomial program starts from zero and returns the exact field value. -/
theorem polynomial_value (terms : List PolynomialTerm) (values : Fin 4 → BN254.BaseField)
    (sourceValue : PolynomialTerm → BN254.BaseField) (base : Memory)
    (sources : ∀ term ∈ terms, PolynomialSource term base.ram (base.registers 10) (sourceValue term))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (values factor).val) :
    (executeLinear (polynomial terms) base).registers 4 = BitVec.ofNat 256
      (terms.foldl (fun (sum : BN254.BaseField) (term : PolynomialTerm) => sum + term.factors.foldl (fun product factor => product * values factor) (sourceValue term)) 0).val := by
  rw [polynomial, executeLinear_append]
  apply polynomialBody_value terms values sourceValue (executeLinear [.constant 4 0] base) 0
  · simpa [executeLinear, LinearInstruction.execute] using sources
  · intro factor
    have different : polynomialFactorRegister factor ≠ 4 := by
      intro same; have value := congrArg Fin.val same; simp [polynomialFactorRegister] at value; omega
    simpa [executeLinear, LinearInstruction.execute, different] using encoded factor
  · simp [executeLinear, LinearInstruction.execute]

/-- The polynomial budget charges initialization and every emitted term instruction. -/
theorem polynomial_length (terms : List PolynomialTerm) :
    (polynomial terms).length = 1 + (terms.map (fun term =>
      (if term.folded then 1272 else 3) + term.factors.length + 1)).sum := by
  simp [polynomial, List.length_flatMap, polynomialTerm_length]; omega

end Kriterion.ArgoMAC.ArithmeticSimulator
