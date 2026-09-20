import Proof.Privacy.Simulator.Arithmetic.HashLiftInteger

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Word multiplication keeps the exact product modulo the word width. -/
theorem wordMul_nat (left right : Nat) :
    Arithmetic.mul.eval (BitVec.ofNat 256 left) (BitVec.ofNat 256 right) = BitVec.ofNat 256 (left * right) :=
  (BitVec.ofNat_mul left right).symm

/-- Word addition keeps the exact sum modulo the word width. -/
theorem wordAdd_nat (left right : Nat) :
    Arithmetic.add.eval (BitVec.ofNat 256 left) (BitVec.ofNat 256 right) = BitVec.ofNat 256 (left + right) :=
  (BitVec.ofNat_add left right).symm

/-- The fixed mask selects the low 128-bit limb. -/
theorem wordMask128_nat (value : Nat) :
    Arithmetic.and.eval (BitVec.ofNat 256 value) (BitVec.ofNat 256 (2 ^ 128 - 1)) = BitVec.ofNat 256 (value % 2 ^ 128) := by
  change BitVec.ofNat 256 value &&& BitVec.ofNat 256 (2 ^ 128 - 1) = _
  rw [← BitVec.ofNat_and, Nat.and_two_pow_sub_one_eq_mod]

/-- The fixed shift selects the high limb of a complete machine word. -/
theorem wordShift128_nat (value : Nat) (fits : value < 2 ^ 256) :
    Arithmetic.shiftRight.eval (BitVec.ofNat 256 value) 128 = BitVec.ofNat 256 (value / 2 ^ 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  have divided : value / 2 ^ 128 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self _ _) fits
  simp [Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt divided).symm

end Kriterion.ArgoMAC.ArithmeticSimulator
