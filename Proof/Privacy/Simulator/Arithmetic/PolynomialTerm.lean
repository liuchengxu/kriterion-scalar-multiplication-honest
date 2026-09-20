import Proof.Privacy.Simulator.Arithmetic.PolynomialFactors

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A term source consists of one canonical coefficient or 254 canonical field words. -/
def PolynomialSource (term : PolynomialTerm) (ram : Word → Word) (pointer : Word) (value : BN254.BaseField) : Prop :=
  if term.folded then ∃ values : Fin 254 → BN254.BaseField, DigitAdaptor.fromBits values = value ∧
    ∀ index, ram (pointer + BitVec.ofNat 256 (term.offset + index.val)) = BitVec.ofNat 256 (values index).val
  else ram (pointer + BitVec.ofNat 256 term.offset) = BitVec.ofNat 256 value.val

/-- A term read preserves every source component and each register above three. -/
theorem polynomialTermRead_preserves (term : PolynomialTerm) (base : Memory) :
    (executeLinear (polynomialTermRead term) base).ram = base.ram ∧
    (executeLinear (polynomialTermRead term) base).bits = base.bits ∧
    ∀ register : Register, 4 ≤ register.val →
      (executeLinear (polynomialTermRead term) base).registers register = base.registers register := by
  unfold polynomialTermRead
  split
  · exact fieldFold_preserves _ _ _
  · refine ⟨rfl, rfl, ?_⟩
    intro register caller
    have notZero : register ≠ 0 := by intro same; have value := congrArg Fin.val same; omega
    have notTwo : register ≠ 2 := by intro same; have value := congrArg Fin.val same; omega
    simp [executeLinear, LinearInstruction.execute, notZero, notTwo]

/-- A term read returns its exact typed source value. -/
theorem polynomialTermRead_value (term : PolynomialTerm) (base : Memory) (value : BN254.BaseField)
    (source : PolynomialSource term base.ram (base.registers 10) value) :
    (executeLinear (polynomialTermRead term) base).registers 0 = BitVec.ofNat 256 value.val := by
  unfold polynomialTermRead
  split
  · rename_i folded
    obtain ⟨values, result, stored⟩ := by simpa [PolynomialSource, folded] using source
    rw [← result]
    exact fieldFold_value 254 term.offset values base stored
  · rename_i folded
    have stored : base.ram (base.registers 10 + BitVec.ofNat 256 term.offset) = BitVec.ofNat 256 value.val := by
      simpa [PolynomialSource, folded] using source
    simpa [executeLinear, LinearInstruction.execute, Arithmetic.eval] using stored

/-- The compiled term charges every read, factor, and accumulator sum. -/
theorem polynomialTerm_length (term : PolynomialTerm) :
    (polynomialTerm term).length = (if term.folded then 1272 else 3) + term.factors.length + 1 := by
  simp only [polynomialTerm, polynomialTermRead, List.length_append, polynomialFactors_length, List.length_singleton]
  split <;> simp [fieldFold_length] <;> omega

/-- The compiled term preserves all source data and registers above four. -/
theorem polynomialTerm_preserves (term : PolynomialTerm) (base : Memory) :
    (executeLinear (polynomialTerm term) base).ram = base.ram ∧
    (executeLinear (polynomialTerm term) base).bits = base.bits ∧
    ∀ register : Register, 5 ≤ register.val →
      (executeLinear (polynomialTerm term) base).registers register = base.registers register := by
  rw [polynomialTerm, executeLinear_append, executeLinear_append]
  have read := polynomialTermRead_preserves term base
  have product := polynomialFactors_preserves term.factors (executeLinear (polynomialTermRead term) base)
  refine ⟨product.1.trans read.1, product.2.1.trans read.2.1, ?_⟩
  intro register caller
  have notZero : register ≠ 0 := by intro same; have value := congrArg Fin.val same; omega
  have notFour : register ≠ 4 := by intro same; have value := congrArg Fin.val same; omega
  simp only [executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute, Function.update_of_ne notFour]
  exact (product.2.2 register notZero).trans (read.2.2 register (by omega))

/-- The compiled term adds its exact product to the typed polynomial accumulator. -/
theorem polynomialTerm_value (term : PolynomialTerm) (values : Fin 4 → BN254.BaseField)
    (base : Memory) (value accumulator : BN254.BaseField)
    (source : PolynomialSource term base.ram (base.registers 10) value)
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (values factor).val)
    (initial : base.registers 4 = BitVec.ofNat 256 accumulator.val) :
    (executeLinear (polynomialTerm term) base).registers 4 =
      BitVec.ofNat 256 (accumulator + term.factors.foldl (fun product factor => product * values factor) value).val := by
  have read := polynomialTermRead_preserves term base
  have product := polynomialFactors_preserves term.factors (executeLinear (polynomialTermRead term) base)
  have result := polynomialFactors_value term.factors values (executeLinear (polynomialTermRead term) base) value
    (polynomialTermRead_value term base value source) (fun factor => by
      rw [read.2.2 (polynomialFactorRegister factor) (by change 4 ≤ 5 + factor.val; omega)]
      exact encoded factor)
  rw [polynomialTerm, executeLinear_append, executeLinear_append]
  change Arithmetic.fieldAdd.eval
    ((executeLinear (polynomialFactors term.factors) (executeLinear (polynomialTermRead term) base)).registers 4)
    ((executeLinear (polynomialFactors term.factors) (executeLinear (polynomialTermRead term) base)).registers 0) = _
  rw [result, product.2.2 4 (by decide), read.2.2 4 (by decide), initial, fieldAdd_words]

end Kriterion.ArgoMAC.ArithmeticSimulator
