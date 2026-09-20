import Proof.Privacy.Simulator.Arithmetic.RetargetCurveSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
attribute [local irreducible] gateRetarget gatePolynomial polynomial retargetProgram

/-- The request prefix retains all four polynomial factors. -/
theorem retargetAtPrepared_factors (sourceOffset targetOffset : Nat) (memory : Memory) (input : AffineInput)
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val) :
    ∀ factor, (retargetAtPrepared sourceOffset 14 targetOffset memory).registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val := by
  intro factor
  have factorBound : (polynomialFactorRegister factor).val < 10 := by fin_cases factor <;> decide
  have notTen : polynomialFactorRegister factor ≠ 10 := by intro same; have vals := congrArg Fin.val same; omega
  have notThirteen : polynomialFactorRegister factor ≠ 13 := by intro same; have vals := congrArg Fin.val same; omega
  simpa only [retargetAtPrepared, Function.update_of_ne notThirteen, Function.update_of_ne notTen] using encoded factor

/-- The selected X request writes its exact typed low target. -/
theorem xRetargetAt_ram (sample : XPublicSample) (input : AffineInput) (memory : Memory) (target : BaseField)
    (sourceOffset targetOffset : Nat)
    (stored : WordsAt memory.ram (memory.registers 11) sourceOffset ((gateDataSchedule 5 4).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : memory.ram (memory.registers 14 + BitVec.ofNat 256 targetOffset) = BitVec.ofNat 256 target.val) :
    (executeLinear (retargetAt .x sourceOffset 14 targetOffset) memory).ram =
      Function.update memory.ram (memory.registers 11 + BitVec.ofNat 256 sourceOffset + 762)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  let prepared := retargetAtPrepared sourceOffset 14 targetOffset memory
  have sourcePointer : prepared.registers 10 = memory.registers 11 + BitVec.ofNat 256 sourceOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_of_ne (by decide : (10 : Register) ≠ 13), Function.update_self]
  have targetPointer : prepared.registers 13 = memory.registers 14 + BitVec.ofNat 256 targetOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_self]
  have storedPrepared : WordsAt prepared.ram (prepared.registers 10) 0 ((gateDataSchedule 5 4).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)) := by
    rw [sourcePointer]
    exact wordsAt_rebase stored
  have result := xRetarget_ram sample input prepared target storedPrepared
    (retargetAtPrepared_factors sourceOffset targetOffset memory input encoded)
    (by rw [targetPointer]; exact requested)
  rw [retargetAt_memory .x sourceOffset 14 targetOffset memory (by decide) (by decide), retargetCode_eq, retargetProgram]
  change (executeLinear (gateRetarget xTerms 3) prepared).ram = _
  rw [result, sourcePointer]
  rfl

/-- The selected Y request writes its exact typed low target. -/
theorem yRetargetAt_ram (sample : YPublicSample) (input : AffineInput) (memory : Memory) (target : BaseField)
    (sourceOffset targetOffset : Nat)
    (stored : WordsAt memory.ram (memory.registers 11) sourceOffset ((gateDataSchedule 4 3).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : memory.ram (memory.registers 14 + BitVec.ofNat 256 targetOffset) = BitVec.ofNat 256 target.val) :
    (executeLinear (retargetAt .y sourceOffset 14 targetOffset) memory).ram =
      Function.update memory.ram (memory.registers 11 + BitVec.ofNat 256 sourceOffset + 508)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  let prepared := retargetAtPrepared sourceOffset 14 targetOffset memory
  have sourcePointer : prepared.registers 10 = memory.registers 11 + BitVec.ofNat 256 sourceOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_of_ne (by decide : (10 : Register) ≠ 13), Function.update_self]
  have targetPointer : prepared.registers 13 = memory.registers 14 + BitVec.ofNat 256 targetOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_self]
  have storedPrepared : WordsAt prepared.ram (prepared.registers 10) 0 ((gateDataSchedule 4 3).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)) := by
    rw [sourcePointer]
    exact wordsAt_rebase stored
  have result := yRetarget_ram sample input prepared target storedPrepared
    (retargetAtPrepared_factors sourceOffset targetOffset memory input encoded)
    (by rw [targetPointer]; exact requested)
  rw [retargetAt_memory .y sourceOffset 14 targetOffset memory (by decide) (by decide), retargetCode_eq, retargetProgram]
  change (executeLinear (gateRetarget yTerms 2) prepared).ram = _
  rw [result, sourcePointer]
  rfl

/-- The selected Z request writes its exact typed low target. -/
theorem zRetargetAt_ram (sample : ZPublicSample) (input : AffineInput) (memory : Memory) (target : BaseField)
    (sourceOffset targetOffset : Nat)
    (stored : WordsAt memory.ram (memory.registers 11) sourceOffset ((gateDataSchedule 5 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : memory.ram (memory.registers 14 + BitVec.ofNat 256 targetOffset) = BitVec.ofNat 256 target.val) :
    (executeLinear (retargetAt .z sourceOffset 14 targetOffset) memory).ram =
      Function.update memory.ram (memory.registers 11 + BitVec.ofNat 256 sourceOffset + 1016)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x9Targets 0).val) := by
  let prepared := retargetAtPrepared sourceOffset 14 targetOffset memory
  have sourcePointer : prepared.registers 10 = memory.registers 11 + BitVec.ofNat 256 sourceOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_of_ne (by decide : (10 : Register) ≠ 13), Function.update_self]
  have targetPointer : prepared.registers 13 = memory.registers 14 + BitVec.ofNat 256 targetOffset := by
    simp only [prepared, retargetAtPrepared, Function.update_self]
  have storedPrepared : WordsAt prepared.ram (prepared.registers 10) 0 ((gateDataSchedule 5 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)) := by
    rw [sourcePointer]
    exact wordsAt_rebase stored
  have result := zRetarget_ram sample input prepared target storedPrepared
    (retargetAtPrepared_factors sourceOffset targetOffset memory input encoded)
    (by rw [targetPointer]; exact requested)
  rw [retargetAt_memory .z sourceOffset 14 targetOffset memory (by decide) (by decide), retargetCode_eq, retargetProgram]
  change (executeLinear (gateRetarget zTerms 4) prepared).ram = _
  rw [result, sourcePointer]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
