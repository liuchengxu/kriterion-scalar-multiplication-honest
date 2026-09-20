import Proof.Privacy.Simulator.Arithmetic.PrivateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

private theorem fixedFlatMap_injective {A : Type} (encode : A → List Word) (width : Nat)
    (length : ∀ value, (encode value).length = width) (injective : Function.Injective encode)
    (left right : List A) (sameLength : left.length = right.length)
    (same : left.flatMap encode = right.flatMap encode) : left = right := by
  induction left generalizing right with
  | nil => simpa using sameLength.symm
  | cons head tail ih =>
    cases right with
    | nil => simp at sameLength
    | cons other rest =>
      have split := List.append_inj same ((length head).trans (length other).symm)
      have heads := injective split.1
      have tails := ih rest (by simpa using sameLength) split.2
      simp [heads, tails]

/-- A count cast preserves the unique representation of each source value. -/
theorem PrivateSchedule.cast_injective {A : Type} {first second : Nat} {source : Code A first}
    (schedule : PrivateSchedule source) (same : first = second)
    (injective : Function.Injective schedule.words) : Function.Injective (schedule.cast same).words := by
  cases same
  exact injective

/-- A source equivalence preserves the unique word representation. -/
theorem PrivateSchedule.equiv_injective {A B : Type} {count : Nat} {source : Code A count}
    (schedule : PrivateSchedule source) (transform : A ≃ B)
    (injective : Function.Injective schedule.words) : Function.Injective (schedule.equiv transform).words :=
  injective.comp transform.symm.injective

/-- Fixed word counts keep the two source values separate. -/
theorem PrivateSchedule.pair_injective {A B : Type} {first second : Nat}
    {left : Code A first} {right : Code B second}
    (leftSchedule : PrivateSchedule left) (rightSchedule : PrivateSchedule right)
    (leftInjective : Function.Injective leftSchedule.words)
    (rightInjective : Function.Injective rightSchedule.words) :
    Function.Injective (leftSchedule.pair rightSchedule).words := by
  intro a b same
  have split := List.append_inj same
    ((rightSchedule.wordsLength a.2).trans (rightSchedule.wordsLength b.2).symm)
  exact Prod.ext (leftInjective split.2) (rightInjective split.1)

/-- Each fixed vector has a unique sequence of source words. -/
theorem PrivateSchedule.vector_injective {A : Type} {draws : Nat} {source : Code A draws}
    (schedule : PrivateSchedule source) (count : Nat)
    (injective : Function.Injective schedule.words) : Function.Injective (schedule.vector count).words := by
  intro a b same
  apply Vector.toList_inj.mp
  exact fixedFlatMap_injective schedule.words draws schedule.wordsLength injective a.toList b.toList
    (by simp) same

private theorem naturalWord_injective {A : Type} (value : A → Nat)
    (injective : Function.Injective value) (fits : ∀ a, value a < 2 ^ 256) :
    Function.Injective (fun a => [BitVec.ofNat 256 (value a)]) := by
  intro a b same
  have words : BitVec.ofNat 256 (value a) = BitVec.ofNat 256 (value b) := List.cons.inj same |>.1
  have values := congrArg BitVec.toNat words
  exact injective (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fits a), Nat.mod_eq_of_lt (fits b)] using values)

/-- Each field word identifies its source field value. -/
theorem fieldSchedule_injective : Function.Injective fieldSchedule.words :=
  naturalWord_injective ZMod.val (ZMod.val_injective _) (fun value =>
    value.val_lt.trans (by decide : BN254.baseFieldModulus < 2 ^ 256))

/-- Each quotient word identifies its source integer. -/
theorem quotientSchedule_injective : Function.Injective quotientSchedule.words :=
  naturalWord_injective Fin.val Fin.val_injective (fun value =>
    value.isLt.trans (by decide : Security.hashLiftQuotientCount < 2 ^ 256))

/-- Widening a bit block keeps every source bit. -/
theorem bitsSchedule_injective (width : Nat) (fits : width ≤ 256) :
    Function.Injective (bitsSchedule width fits).words := by
  intro a b same
  have words : a.setWidth 256 = b.setWidth 256 := List.cons.inj same |>.1
  have aFits : a.toNat < 2 ^ 256 := a.isLt.trans_le (Nat.pow_le_pow_right (by decide) fits)
  have bFits : b.toNat < 2 ^ 256 := b.isLt.trans_le (Nat.pow_le_pow_right (by decide) fits)
  apply BitVec.eq_of_toNat_eq
  have values := congrArg BitVec.toNat words
  simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt aFits, Nat.mod_eq_of_lt bFits] using values

/-- Each table word identifies its random row. -/
theorem tableSchedule_injective : Function.Injective tableSchedule.words :=
  PrivateSchedule.equiv_injective _ _ (bitsSchedule_injective 256 (by decide))

/-- Gate arrays retain every private source value. -/
theorem gateArraysSchedule_injective (coefficients gates : Nat) :
    Function.Injective (gateArraysSchedule coefficients gates).words :=
  PrivateSchedule.cast_injective _ _
    (PrivateSchedule.pair_injective _ _
      (PrivateSchedule.vector_injective _ _ fieldSchedule_injective)
      (PrivateSchedule.pair_injective _ _
        (PrivateSchedule.vector_injective _ _ (PrivateSchedule.vector_injective _ _ tableSchedule_injective))
        (PrivateSchedule.pair_injective _ _
          (PrivateSchedule.vector_injective _ _ (PrivateSchedule.vector_injective _ _ quotientSchedule_injective))
          (PrivateSchedule.vector_injective _ _ (PrivateSchedule.vector_injective _ _ fieldSchedule_injective)))))

/-- The gate data representation retains its array values. -/
theorem gateDataSchedule_injective (coefficients gates : Nat) :
    Function.Injective (gateDataSchedule coefficients gates).words :=
  PrivateSchedule.equiv_injective _ _ (gateArraysSchedule_injective coefficients gates)

/-- A row retains its three coordinate records. -/
theorem rowSchedule_injective : Function.Injective rowSchedule.words :=
  PrivateSchedule.equiv_injective _ _ (PrivateSchedule.pair_injective _ _
    (PrivateSchedule.equiv_injective _ _ (gateDataSchedule_injective 5 4))
    (PrivateSchedule.pair_injective _ _
      (PrivateSchedule.equiv_injective _ _ (gateDataSchedule_injective 4 3))
      (PrivateSchedule.equiv_injective _ _ (gateDataSchedule_injective 5 5))))

/-- The public schedule retains its curve and point records. -/
theorem publicSchedule_injective : Function.Injective publicSchedule.words :=
  PrivateSchedule.equiv_injective _ _ (PrivateSchedule.pair_injective _ _
    (PrivateSchedule.equiv_injective _ _ (gateDataSchedule_injective 3 5))
    (PrivateSchedule.vector_injective _ _ rowSchedule_injective))

/-- A label key retains both label blocks. -/
theorem keySchedule_injective : Function.Injective keySchedule.words :=
  PrivateSchedule.equiv_injective _ _ (PrivateSchedule.pair_injective _ _
    (bitsSchedule_injective 128 (by decide)) (bitsSchedule_injective 128 (by decide)))

/-- The input key schedule retains both coordinate keys. -/
theorem inputKeySchedule_injective : Function.Injective inputKeySchedule.words :=
  PrivateSchedule.equiv_injective _ _ (PrivateSchedule.pair_injective _ _
    (PrivateSchedule.vector_injective _ _ keySchedule_injective)
    (PrivateSchedule.vector_injective _ _ keySchedule_injective))

/-- The complete offline word sequence identifies one private source coin. -/
theorem offlineSchedule_injective : Function.Injective offlineSchedule.words :=
  PrivateSchedule.pair_injective _ _ publicSchedule_injective
    (PrivateSchedule.pair_injective _ _ inputKeySchedule_injective fieldSchedule_injective)

end Kriterion.ArgoMAC.ArithmeticSimulator
