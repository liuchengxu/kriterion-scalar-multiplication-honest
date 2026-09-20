import Construction.Simulator.HashLift
import Proof.Privacy.Programming.Gate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security

/-- The first carry comes from the low quotient and target limbs. -/
def liftLowSum (target quotient : Nat) : Nat :=
  (baseFieldModulus % 2 ^ 128) * (quotient % 2 ^ 128) + target % 2 ^ 128

/-- The middle sum includes both cross products and the low carry. -/
def liftMiddleSum (target quotient : Nat) : Nat :=
  (baseFieldModulus % 2 ^ 128) * (quotient / 2 ^ 128) +
    (baseFieldModulus / 2 ^ 128) * (quotient % 2 ^ 128) + target / 2 ^ 128 + liftLowSum target quotient / 2 ^ 128

/-- The high limb includes the high product and the middle carry. -/
def liftHigh (target quotient : Nat) : Nat :=
  (baseFieldModulus / 2 ^ 128) * (quotient / 2 ^ 128) + liftMiddleSum target quotient / 2 ^ 128

/-- Three limbs represent the exact integer lift before bit-vector conversion. -/
theorem lift_limbs (target quotient : Nat) :
    liftLowSum target quotient % 2 ^ 128 +
      2 ^ 128 * (liftMiddleSum target quotient % 2 ^ 128) + 2 ^ 256 * liftHigh target quotient =
      target + baseFieldModulus * quotient := by
  have targetParts := Nat.mod_add_div target (2 ^ 128)
  have quotientParts := Nat.mod_add_div quotient (2 ^ 128)
  have lowParts := Nat.mod_add_div (liftLowSum target quotient) (2 ^ 128)
  have middleParts := Nat.mod_add_div (liftMiddleSum target quotient) (2 ^ 128)
  unfold liftHigh liftMiddleSum liftLowSum at *
  norm_num [baseFieldModulus] at *
  omega

/-- The low sum fits one machine word. -/
theorem liftLowSum_bound (target quotient : Nat) : liftLowSum target quotient < 2 ^ 256 := by
  have q := Nat.mod_lt quotient (by decide : 0 < 2 ^ 128)
  have t := Nat.mod_lt target (by decide : 0 < 2 ^ 128)
  unfold liftLowSum
  norm_num [baseFieldModulus] at *
  omega

/-- The middle sum fits one machine word for every complete lift quotient. -/
theorem liftMiddleSum_bound (target : BaseField) (quotient : HashLiftQuotient) :
    liftMiddleSum target.val quotient.val < 2 ^ 256 := by
  have q := quotient.isLt
  have t := target.val_lt
  have qlow := Nat.mod_lt quotient.val (by decide : 0 < 2 ^ 128)
  have low := liftLowSum_bound target.val quotient.val
  unfold liftMiddleSum
  norm_num [hashLiftQuotientCount, baseFieldModulus] at *
  omega

/-- The complete lift fits the required 384-bit source range. -/
theorem liftValue_bound (target : BaseField) (quotient : HashLiftQuotient) :
    target.val + baseFieldModulus * quotient.val < 2 ^ 384 :=
  lt_of_lt_of_le (goodHashLiftValue_lt_goodCount target quotient) (Nat.div_mul_le_self _ _)

/-- The high output limb fits 128 bits. -/
theorem liftHigh_bound (target : BaseField) (quotient : HashLiftQuotient) : liftHigh target.val quotient.val < 2 ^ 128 := by
  have value := liftValue_bound target quotient
  have represented := lift_limbs target.val quotient.val
  norm_num at value represented ⊢
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
