import Proof.Privacy.Simulator.Arithmetic.RetargetFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
attribute [local irreducible] gateRetarget gatePolynomial polynomial retargetProgram

/-- The complete curve pass writes the exact low target of the typed retargeted request. -/
theorem retargetCurveCode_ram (sample : CurvePublicSample) (input : AffineInput) (memory : Memory) (target : BaseField)
    (stored : WordsAt memory.ram (memory.registers 11) 834395 ((gateDataSchedule 3 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)))
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (requested : memory.ram (memory.registers 11) = BitVec.ofNat 256 target.val) :
    (executeLinear retargetCurveCode memory).ram =
      Function.update memory.ram (memory.registers 11 + 834903)
        (BitVec.ofNat 256 ((sample.request.retarget input target).x7Targets 0).val) := by
  let loaded := executeLinear retargetInput memory
  let prepared := retargetAtPrepared 834395 11 0 loaded
  have saved := retargetInput_preserves memory
  have factors := retargetInput_values memory input coordinates
  have sourcePointer : prepared.registers 10 = memory.registers 11 + 834395 := by
    simp only [prepared, retargetAtPrepared, Function.update_of_ne (by decide : (10 : Register) ≠ 13),
      Function.update_self, loaded, saved.2.2 11 (by decide), BitVec.ofNat_eq_ofNat]
  have targetPointer : prepared.registers 13 = memory.registers 11 := by
    simp only [prepared, retargetAtPrepared, Function.update_self, show BitVec.ofNat 256 0 = (0 : Word) from rfl, BitVec.add_zero,
      loaded, saved.2.2 11 (by decide)]
    simp
  have ram : prepared.ram = memory.ram := saved.1
  have storedPrepared : WordsAt prepared.ram (prepared.registers 10) 0 ((gateDataSchedule 3 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets)) := by
    rw [ram, sourcePointer]
    exact wordsAt_rebase stored
  have factorsPrepared : ∀ factor, prepared.registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val := by
    intro factor
    have factorBound : (polynomialFactorRegister factor).val < 10 := by fin_cases factor <;> decide
    have notTen : polynomialFactorRegister factor ≠ 10 := by intro same; have vals := congrArg Fin.val same; omega
    have notThirteen : polynomialFactorRegister factor ≠ 13 := by intro same; have vals := congrArg Fin.val same; omega
    simpa only [prepared, retargetAtPrepared, Function.update_of_ne notThirteen, Function.update_of_ne notTen] using factors factor
  have result := curveRetarget_ram sample input prepared target storedPrepared factorsPrepared
    (by rw [ram, targetPointer]; exact requested)
  rw [retargetCurveCode_eq, retargetCurveProgram, executeLinear_append,
    retargetAt_memory .curve 834395 11 0 loaded (by decide) (by decide), retargetCode_eq, retargetProgram]
  change (executeLinear (gateRetarget curveTerms 2) prepared).ram = _
  rw [result, ram, sourcePointer]
  rw [BitVec.add_assoc]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
