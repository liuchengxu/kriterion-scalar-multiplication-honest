import Proof.Privacy.Simulator.Arithmetic.HashLiftProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography.BoundedMachine

/-- Each source limb has its exact little-endian index. -/
def liftLimb (target quotient : Nat) (index : Fin 3) : Nat :=
  if index.val = 0 then liftLowSum target quotient % 2 ^ 128
  else if index.val = 1 then liftMiddleSum target quotient % 2 ^ 128
  else liftHigh target quotient

/-- Every computed source limb fits one 128-bit block. -/
theorem liftLimb_bound (target : BaseField) (quotient : HashLiftQuotient) (index : Fin 3) :
    liftLimb target.val quotient.val index < 2 ^ 128 := by
  fin_cases index
  · exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_lt _ (by decide)
  · exact liftHigh_bound target quotient

/-- The three arithmetic limbs equal the original hash-lift block source. -/
theorem liftHashBlocks_limb (target : BaseField) (quotient : HashLiftQuotient) (index : Fin 3) :
    liftHashBlocks (goodHashLift target quotient).1 index = BitVec.ofNat 128 (liftLimb target.val quotient.val index) := by
  have bounded := liftValue_bound target quotient
  have represented := lift_limbs target.val quotient.val
  have lowBound := Nat.mod_lt (liftLowSum target.val quotient.val) (by decide : 0 < 2 ^ 128)
  have middleBound := Nat.mod_lt (liftMiddleSum target.val quotient.val) (by decide : 0 < 2 ^ 128)
  have highBound := liftHigh_bound target quotient
  fin_cases index <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [liftHashBlocks, goodHashLift, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt bounded, Nat.shiftRight_eq_div_pow, liftLimb] <;>
    norm_num at represented lowBound middleBound highBound ⊢ <;> omega

/-- The lift machine returns the exact original block source in registers four through six. -/
theorem hashLiftProgram_source (base : Memory) (target : BaseField) (quotient : HashLiftQuotient)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (quotientWord : base.registers 1 = BitVec.ofNat 256 quotient.val) (index : Fin 3) :
    (executeLinear hashLiftProgram base).registers ⟨4 + index.val, by omega⟩ =
      (liftHashBlocks (goodHashLift target quotient).1 index).setWidth 256 := by
  have output := hashLiftProgram_values base target quotient targetWord quotientWord
  rw [liftHashBlocks_limb]
  have widening : (BitVec.ofNat 128 (liftLimb target.val quotient.val index)).setWidth 256 =
      BitVec.ofNat 256 (liftLimb target.val quotient.val index) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (liftLimb_bound target quotient index)]
  rw [widening]
  fin_cases index
  · exact output.1
  · exact output.2.1
  · exact output.2.2

end Kriterion.ArgoMAC.ArithmeticSimulator
