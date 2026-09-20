import Proof.Privacy.Simulator.Arithmetic.GatePolynomial
import Proof.Privacy.Simulator.Arithmetic.GateRetargetMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- A complete gate update changes only its selected low target. -/
theorem gateRetarget_ram {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (gate : Fin gates) (base : Memory) (target result old : BaseField)
    (computed : (executeLinear (gatePolynomial terms) base).registers 4 = BitVec.ofNat 256 result.val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val)
    (oldWord : base.ram (base.registers 10 + BitVec.ofNat 256 (254 * gate.val)) = BitVec.ofNat 256 old.val) :
    (executeLinear (gateRetarget terms gate) base).ram =
      Function.update base.ram (base.registers 10 + BitVec.ofNat 256 (254 * gate.val))
        (BitVec.ofNat 256 (target - result + old).val) := by
  have saved := polynomial_preserves (terms.map GateTerm.compile) base
  change (executeLinear (gatePolynomial terms) base).ram = base.ram ∧
    (executeLinear (gatePolynomial terms) base).bits = base.bits ∧
    (∀ register : Register, 5 ≤ register.val → (executeLinear (gatePolynomial terms) base).registers register = base.registers register) at saved
  rw [gateRetarget, executeLinear_append]
  rw [gateRetargetFinish_ram _ _ target result old computed
    (by rw [saved.1, saved.2.2 13 (by decide)]; exact requested)
    (by rw [saved.1, saved.2.2 10 (by decide)]; exact oldWord), saved.1, saved.2.2 10 (by decide)]

/-- The curve retarget program writes the exact low target from the source request. -/
theorem curveRetarget_ram (sample : CurvePublicSample) (input : AffineInput) (base : Memory) (target : BaseField)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 3 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val) :
    (executeLinear (gateRetarget curveTerms 2) base).ram =
      Function.update base.ram (base.registers 10 + 508)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x7Targets 0).val) := by
  have low := gateData_target 3 5 (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    base.ram (base.registers 10) 0 2 0 stored
  have result := gateRetarget_ram curveTerms 2 base target (sample.request.result input) (sample.targets 2 0)
    (curvePolynomial_value sample input base stored encoded) requested (by simpa [coordinateBitCount] using low)
  simpa [CurveGateRequest.retarget, retargetBits_low, CurvePublicSample.request] using result

/-- The X retarget program writes the exact low target from the source request. -/
theorem xRetarget_ram (sample : XPublicSample) (input : AffineInput) (base : Memory) (target : BaseField)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 5 4).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val) :
    (executeLinear (gateRetarget xTerms 3) base).ram =
      Function.update base.ram (base.registers 10 + 762)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  have low := gateData_target 5 4 (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    base.ram (base.registers 10) 0 3 0 stored
  have result := gateRetarget_ram xTerms 3 base target (sample.request.result input) (sample.targets 3 0)
    (xPolynomial_value sample input base stored encoded) requested (by simpa [coordinateBitCount] using low)
  simpa [BiquadraticXRequest.retarget, retargetBits_low, XPublicSample.request] using result

/-- The Y retarget program writes the exact low target from the source request. -/
theorem yRetarget_ram (sample : YPublicSample) (input : AffineInput) (base : Memory) (target : BaseField)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 4 3).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val) :
    (executeLinear (gateRetarget yTerms 2) base).ram =
      Function.update base.ram (base.registers 10 + 508)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  have low := gateData_target 4 3 (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    base.ram (base.registers 10) 0 2 0 stored
  have result := gateRetarget_ram yTerms 2 base target (sample.request.result input) (sample.targets 2 0)
    (yPolynomial_value sample input base stored encoded) requested (by simpa [coordinateBitCount] using low)
  simpa [BiquadraticYRequest.retarget, retargetBits_low, YPublicSample.request] using result

/-- The Z retarget program writes the exact low target from the source request. -/
theorem zRetarget_ram (sample : ZPublicSample) (input : AffineInput) (base : Memory) (target : BaseField)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule 5 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : base.ram (base.registers 13) = BitVec.ofNat 256 target.val) :
    (executeLinear (gateRetarget zTerms 4) base).ram =
      Function.update base.ram (base.registers 10 + 1016)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  have low := gateData_target 5 5 (sample.coefficients, sample.tables, sample.quotients, sample.targets)
    base.ram (base.registers 10) 0 4 0 stored
  have result := gateRetarget_ram zTerms 4 base target (sample.request.result input) (sample.targets 4 0)
    (zPolynomial_value sample input base stored encoded) requested (by simpa [coordinateBitCount] using low)
  simpa [BiquadraticZRequest.retarget, retargetBits_low, ZPublicSample.request] using result

/-- Every complete gate update preserves its source pointers and all protocol stacks. -/
theorem gateRetarget_preserves {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (gate : Fin gates) (base : Memory) :
    (executeLinear (gateRetarget terms gate) base).bits = base.bits ∧
    ∀ register : Register, 5 ≤ register.val → (executeLinear (gateRetarget terms gate) base).registers register = base.registers register := by
  rw [gateRetarget, executeLinear_append]
  have saved := polynomial_preserves (terms.map GateTerm.compile) base
  exact ⟨(gateRetargetFinish_bits _ _).trans saved.2.1, fun register caller =>
    (gateRetargetFinish_caller _ _ register caller).trans (saved.2.2 register caller)⟩

/-- Every gate update charges its polynomial and all eleven retarget instructions. -/
theorem gateRetarget_length {coefficients gates : Nat} (terms : List (GateTerm coefficients gates)) (gate : Fin gates) :
    (gateRetarget terms gate).length = (gatePolynomial terms).length + 11 := by
  simp only [gateRetarget, List.length_append, gateRetargetFinish_length]

end Kriterion.ArgoMAC.ArithmeticSimulator
