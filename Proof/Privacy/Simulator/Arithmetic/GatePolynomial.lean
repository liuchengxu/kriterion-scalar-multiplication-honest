import Proof.Privacy.Simulator.Arithmetic.GatePolynomialSource
import Proof.Privacy.Distribution.PublicSample

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The four preserved factor registers hold x, y, x squared, and y squared. -/
def polynomialInput (input : AffineInput) : Fin 4 → BaseField := ![input.x, input.y, input.x ^ 2, input.y ^ 2]

/-- The curve program evaluates the original curve request result. -/
theorem curvePolynomial_value (sample : CurvePublicSample) (input : AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 3 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val) :
    (executeLinear (gatePolynomial curveTerms) base).registers 4 = BitVec.ofNat 256 (sample.request.result input).val := by
  have result := gatePolynomial_value curveTerms (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    (polynomialInput input) base stored encoded
  simpa [curveTerms, GateTerm.factors, GateTerm.value, polynomialInput, CurvePublicSample.request, CurveGateRequest.result,
    pow_succ, mul_assoc] using result

/-- The X program evaluates the original X request result. -/
theorem xPolynomial_value (sample : XPublicSample) (input : AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 5 4).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val) :
    (executeLinear (gatePolynomial xTerms) base).registers 4 = BitVec.ofNat 256 (sample.request.result input).val := by
  have result := gatePolynomial_value xTerms (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    (polynomialInput input) base stored encoded
  simpa [xTerms, GateTerm.factors, GateTerm.value, polynomialInput, XPublicSample.request, BiquadraticXRequest.result,
    pow_succ, mul_assoc] using result

/-- The Y program evaluates the original Y request result. -/
theorem yPolynomial_value (sample : YPublicSample) (input : AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 4 3).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val) :
    (executeLinear (gatePolynomial yTerms) base).registers 4 = BitVec.ofNat 256 (sample.request.result input).val := by
  have result := gatePolynomial_value yTerms (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    (polynomialInput input) base stored encoded
  simpa [yTerms, GateTerm.factors, GateTerm.value, polynomialInput, YPublicSample.request, BiquadraticYRequest.result,
    pow_succ, mul_assoc] using result

/-- The Z program evaluates the original Z request result. -/
theorem zPolynomial_value (sample : ZPublicSample) (input : AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 5 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val) :
    (executeLinear (gatePolynomial zTerms) base).registers 4 = BitVec.ofNat 256 (sample.request.result input).val := by
  have result := gatePolynomial_value zTerms (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    (polynomialInput input) base stored encoded
  simpa [zTerms, GateTerm.factors, GateTerm.value, polynomialInput, ZPublicSample.request, BiquadraticZRequest.result,
    pow_succ, mul_assoc] using result

/-- The curve program charges all 6384 fixed instructions. -/
theorem curvePolynomial_length : (gatePolynomial curveTerms).length = 6384 := by
  rw [gatePolynomial, polynomial_length]
  simp [curveTerms, GateTerm.compile]

/-- The X program charges all 5120 fixed instructions. -/
theorem xPolynomial_length : (gatePolynomial xTerms).length = 5120 := by
  rw [gatePolynomial, polynomial_length]
  simp [xTerms, GateTerm.compile]

/-- The Y program charges all 3842 fixed instructions. -/
theorem yPolynomial_length : (gatePolynomial yTerms).length = 3842 := by
  rw [gatePolynomial, polynomial_length]
  simp [yTerms, GateTerm.compile]

/-- The Z program charges all 6394 fixed instructions. -/
theorem zPolynomial_length : (gatePolynomial zTerms).length = 6394 := by
  rw [gatePolynomial, polynomial_length]
  simp [zTerms, GateTerm.compile]

end Kriterion.ArgoMAC.ArithmeticSimulator
