/-
This file bounds active pad collisions and proves fresh pivot marginals.
-/

import Proof.Privacy.Distribution.PublicDistribution
import Proof.Privacy.Programming.ProgrammingBridge

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

local instance : NeZero coordinateBitCount := ⟨by decide⟩

theorem fieldBytes_injective : Function.Injective BitAdaptor.fieldBytes := by
  intro a b equal
  apply ZMod.val_injective baseFieldModulus
  have values := congrArg BitVec.toNat equal
  simp only [BitAdaptor.fieldBytes, BitVec.toNat_ofNat] at values
  have bound : baseFieldModulus < 2 ^ 256 := by decide
  rwa [Nat.mod_eq_of_lt (lt_trans a.val_lt bound),
    Nat.mod_eq_of_lt (lt_trans b.val_lt bound)] at values

theorem targetPadBlocks_injective (table : BitAdaptor.Table) :
    Function.Injective (targetPadBlocks table) := by
  intro a b equal
  apply fieldBytes_injective
  have blocks := congrArg (fun blocks : Fin 2 → Block => blocks 1 ++ blocks 0) equal
  rw [targetPadBlocks_value, targetPadBlocks_value] at blocks
  exact (BitVec.xor_right_inj table.trueRow).mp blocks

/-- Either pad block has at most one full block of field preimages. -/
theorem targetPadBlocks_fiber_card [Fintype Block]
    (table : BitAdaptor.Table) (slot : Fin 2) (block : Block) :
    Fintype.card {target : BaseField // targetPadBlocks table target slot = block} ≤
      Fintype.card Block := by
  classical
  apply Fintype.card_le_of_injective
    (fun target : {target : BaseField // targetPadBlocks table target slot = block} =>
      targetPadBlocks table target.val slot.rev)
  intro a b equal
  apply Subtype.ext
  apply targetPadBlocks_injective table
  funext index
  have same := a.property.trans b.property.symm
  fin_cases slot <;> fin_cases index <;> first | exact same | exact equal

/-- This bound holds for each fixed ciphertext and either pad block. -/
theorem targetPadBlocks_mass_le [Fintype Block]
    (table : BitAdaptor.Table) (slot : Fin 2) (block : Block) :
    (PMF.uniformOfFintype BaseField).toOuterMeasure
      {target | targetPadBlocks table target slot = block} ≤
      (Fintype.card Block : ENNReal) / baseFieldModulus := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ZMod.card]
  exact ENNReal.div_le_div_right
    (Nat.cast_le.mpr (targetPadBlocks_fiber_card table slot block)) _

private def subtractFieldEquiv (offset : BaseField) : BaseField ≃ BaseField :=
  (show Function.Involutive (fun seed : BaseField => offset - seed) by
    intro seed
    ring).toPerm _

theorem uniform_subtract_field (offset : BaseField) :
    (PMF.uniformOfFintype BaseField).map (fun seed => offset - seed) =
      PMF.uniformOfFintype BaseField :=
  map_uniformOfFintype_equivBetween (subtractFieldEquiv offset)

private def scaleFieldEquiv (scale inverse : BaseField) (cancel : inverse * scale = 1) :
    BaseField ≃ BaseField where
  toFun value := scale * value
  invFun value := inverse * value
  left_inv value := by
    show inverse * (scale * value) = value
    rw [← mul_assoc, cancel, one_mul]
  right_inv value := by
    show scale * (inverse * value) = value
    rw [← mul_assoc, mul_comm scale inverse, cancel, one_mul]

/-- Scaling by a unit permutes the field, so it preserves the uniform seed. -/
theorem uniform_scale_field (scale inverse : BaseField) (cancel : inverse * scale = 1) :
    (PMF.uniformOfFintype BaseField).map (fun seed => scale * seed) =
      PMF.uniformOfFintype BaseField :=
  map_uniformOfFintype_equivBetween (scaleFieldEquiv scale inverse cancel)

/-- Two is a unit in the BN254 coordinate field. -/
def twoInverse : BaseField :=
  ((baseFieldModulus + 1) / 2 : Nat)

theorem twoInverse_cancel : twoInverse * 2 = 1 := by decide

/-- The pivot transport preserves a fresh independent hash quotient. -/
theorem uniform_subtract_field_quotient (offset : BaseField) :
    (PMF.uniformOfFintype (BaseField × HashLiftQuotient)).map
      (fun seed => (offset - seed.1, seed.2)) =
        PMF.uniformOfFintype (BaseField × HashLiftQuotient) :=
  map_uniformOfFintype_equivBetween
    ((subtractFieldEquiv offset).prodCongr (Equiv.refl HashLiftQuotient))

/-- A fixed offset preserves the field seed and the pad bound. -/
theorem shifted_targetPadBlocks_mass_le [Fintype Block]
    (table : BitAdaptor.Table) (offset : BaseField) (slot : Fin 2) (block : Block) :
    (PMF.uniformOfFintype BaseField).toOuterMeasure
      {seed | targetPadBlocks table (offset - seed) slot = block} ≤
      (Fintype.card Block : ENNReal) / baseFieldModulus := by
  have bound := targetPadBlocks_mass_le table slot block
  rw [← uniform_subtract_field offset, PMF.toOuterMeasure_map_apply] at bound
  rw [Set.preimage_setOf_eq] at bound
  exact bound

/-- The comparison may depend on the prefix, but the field target is fresh. -/
theorem fresh_targetPadBlocks_collision_le [Fintype Block]
    {Prefix : Type*} (prior : PMF Prefix) (table : Prefix → BitAdaptor.Table)
    (slot : Fin 2) (comparison : Prefix → Block) :
    (∑' state, prior state * (PMF.uniformOfFintype BaseField).toOuterMeasure
      {target | targetPadBlocks (table state) target slot = comparison state}) ≤
      (Fintype.card Block : ENNReal) / baseFieldModulus := by
  calc
    _ ≤ ∑' state, prior state *
        ((Fintype.card Block : ENNReal) / baseFieldModulus) :=
      ENNReal.tsum_le_tsum fun state => mul_le_mul_right
        (targetPadBlocks_mass_le (table state) slot (comparison state)) _
    _ = _ := by rw [ENNReal.tsum_mul_right, prior.tsum_coe, one_mul]

theorem goodHashLiftBlocks_injective :
    Function.Injective (fun sample : BaseField × HashLiftQuotient =>
      liftHashBlocks (goodHashLift sample.1 sample.2).1) := by
  intro a b equal
  apply goodHashLiftEquiv.symm.injective
  apply Fin.ext
  have same := congrArg BitVec.toNat (hashLiftBlockEquiv.injective equal)
  simpa only [goodHashLift_toNat] using same

/-- The other two blocks identify each member of a fixed-block fiber. -/
theorem goodHashLiftBlocks_fiber_card [Fintype Block]
    (slot : Fin 3) (block : Block) :
    Fintype.card {sample : BaseField × HashLiftQuotient //
      liftHashBlocks (goodHashLift sample.1 sample.2).1 slot = block} ≤
        Fintype.card Block ^ 2 := by
  classical
  have bound := Fintype.card_le_of_injective
    (fun sample : {sample : BaseField × HashLiftQuotient //
      liftHashBlocks (goodHashLift sample.1 sample.2).1 slot = block} =>
        fun index : {index : Fin 3 // index ≠ slot} =>
          liftHashBlocks (goodHashLift sample.val.1 sample.val.2).1 index.val)
    (by
      intro a b equal
      apply Subtype.ext
      apply goodHashLiftBlocks_injective
      funext index
      by_cases same : index = slot
      · subst index
        exact a.property.trans b.property.symm
      · exact congrFun equal ⟨index, same⟩)
  have count : Fintype.card {index : Fin 3 // index ≠ slot} = 2 := by
    fin_cases slot <;> decide
  simpa only [Fintype.card_fun, count] using bound

private theorem uniform_mass_le_card {Sample : Type} [Fintype Sample] [Nonempty Sample]
    (event : Set Sample) [Fintype event] (bound : Nat) (bounded : Fintype.card event ≤ bound) :
    (PMF.uniformOfFintype Sample).toOuterMeasure event ≤
      (bound : ENNReal) / Fintype.card Sample := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr bounded) _

/-- Good lifts have a small density increase over full uniform hash values. -/
theorem goodHashLiftBlocks_mass_le [Fintype Block]
    (slot : Fin 3) (block : Block) :
    (PMF.uniformOfFintype (BaseField × HashLiftQuotient)).toOuterMeasure
      {sample | liftHashBlocks (goodHashLift sample.1 sample.2).1 slot = block} ≤
        (Fintype.card Block : ENNReal) ^ 2 /
          (baseFieldModulus * hashLiftQuotientCount : Nat) := by
  classical
  have bound := uniform_mass_le_card
    {sample : BaseField × HashLiftQuotient |
      liftHashBlocks (goodHashLift sample.1 sample.2).1 slot = block}
    (Fintype.card Block ^ 2) (goodHashLiftBlocks_fiber_card slot block)
  simpa only [Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.cast_pow] using bound

/-- This collision bound allows any prefix and one fresh field-quotient pair. -/
theorem fresh_goodHashLiftBlocks_collision_le [Fintype Block]
    {Prefix : Type*} (prior : PMF Prefix) (slot : Fin 3)
    (comparison : Prefix → Block) :
    (∑' state, prior state *
      (PMF.uniformOfFintype (BaseField × HashLiftQuotient)).toOuterMeasure
        {sample | liftHashBlocks (goodHashLift sample.1 sample.2).1 slot = comparison state}) ≤
      (Fintype.card Block : ENNReal) ^ 2 /
        (baseFieldModulus * hashLiftQuotientCount : Nat) := by
  calc
    _ ≤ ∑' state, prior state * ((Fintype.card Block : ENNReal) ^ 2 /
        (baseFieldModulus * hashLiftQuotientCount : Nat)) :=
      ENNReal.tsum_le_tsum fun state => mul_le_mul_right
        (goodHashLiftBlocks_mass_le slot (comparison state)) _
    _ = _ := by rw [ENNReal.tsum_mul_right, prior.tsum_coe, one_mul]

private theorem fromBits_update_zero {count : Nat}
    (values : Fin (count + 1) → BaseField) (seed : BaseField) :
    DigitAdaptor.fromBits (Function.update values 0 seed) =
      DigitAdaptor.fromBits values + seed - values 0 := by
  rw [DigitAdaptor.fromBits, DigitAdaptor.fromBits, Fin.foldr_succ, Fin.foldr_succ]
  simp_rw [Function.update_self, Function.update_of_ne (Fin.succ_ne_zero _)]
  ring

/-- Updating position one of a digit target moves position zero of its tail. -/
private theorem fromBits_tail_update_one {count : Nat}
    (values : Fin (count + 2) → BaseField) (seed : BaseField) :
    DigitAdaptor.fromBits (fun index : Fin (count + 1) =>
        Function.update values 1 seed index.succ) =
      DigitAdaptor.fromBits (fun index : Fin (count + 1) => values index.succ) + seed -
        values 1 := by
  have shifted : (fun index : Fin (count + 1) => Function.update values 1 seed index.succ) =
      Function.update (fun index : Fin (count + 1) => values index.succ) 0 seed := by
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · rw [show ((0 : Fin (count + 1)).succ) = (1 : Fin (count + 2)) from by
        apply Fin.ext; simp, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (Fin.succ_ne_zero rest),
        Function.update_of_ne (Fin.ne_of_val_ne (by simp [Fin.val_succ]))]
  rw [shifted, fromBits_update_zero]
  exact congrArg
    (fun value => DigitAdaptor.fromBits (fun index : Fin (count + 1) => values index.succ) +
      seed - value)
    (congrArg values (show ((0 : Fin (count + 1)).succ) = (1 : Fin (count + 2)) from by
      apply Fin.ext; simp))

/-- The free low target masks the retargeted pivot with coefficient minus one. -/
theorem XPublicSample.pivot_seed (sample : XPublicSample)
    (input : AffineInput) (target seed : BaseField) :
    (({sample with targets := (Function.update sample.targets 2
      (Function.update (sample.targets 2) 0 seed))} : XPublicSample).request.retarget
        input target).x9Targets 0 =
      (sample.request.retarget input target).x9Targets 0 + sample.targets 2 0 - seed := by
  simp only [XPublicSample.request, BiquadraticXRequest.retarget,
    BiquadraticXRequest.result, retargetBits, Fin.cases_zero]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Function.update_of_ne (by decide : (3 : Fin 4) ≠ 2)]
  rw [fromBits_update_zero]
  ring

/-- The Y row has one constant-weight adaptor, so the pivot row supplies its own
free seed. Position zero cancels, and position one masks the retargeted pivot with
coefficient minus two. -/
theorem YPublicSample.pivot_seed (sample : YPublicSample)
    (input : AffineInput) (target seed : BaseField) :
    (({sample with targets := (Function.update sample.targets 2
      (Function.update (sample.targets 2) 1 seed))} : YPublicSample).request.retarget
        input target).x9Targets 0 =
      (sample.request.retarget input target).x9Targets 0 +
        2 * sample.targets 2 1 - 2 * seed := by
  simp only [YPublicSample.request, BiquadraticYRequest.retarget,
    BiquadraticYRequest.result, retargetBits, Fin.cases_zero]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2)]
  rw [fromBits_tail_update_one]
  ring

/-- The free low target masks the retargeted pivot with coefficient minus one. -/
theorem ZPublicSample.pivot_seed (sample : ZPublicSample)
    (input : AffineInput) (target seed : BaseField) :
    (({sample with targets := (Function.update sample.targets 2
      (Function.update (sample.targets 2) 0 seed))} : ZPublicSample).request.retarget
        input target).x9Targets 0 =
      (sample.request.retarget input target).x9Targets 0 + sample.targets 2 0 - seed := by
  simp only [ZPublicSample.request, BiquadraticZRequest.retarget,
    BiquadraticZRequest.result, retargetBits, Fin.cases_zero]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 5) ≠ 2),
    Function.update_of_ne (by decide : (1 : Fin 5) ≠ 2),
    Function.update_of_ne (by decide : (3 : Fin 5) ≠ 2),
    Function.update_of_ne (by decide : (4 : Fin 5) ≠ 2)]
  rw [fromBits_update_zero]
  ring

/-- The free low target masks the retargeted pivot with coefficient minus one. -/
theorem CurvePublicSample.pivot_seed (sample : CurvePublicSample)
    (input : AffineInput) (target seed : BaseField) :
    (({sample with targets := (Function.update sample.targets 4
      (Function.update (sample.targets 4) 0 seed))} : CurvePublicSample).request.retarget
        input target).x7Targets 0 =
      (sample.request.retarget input target).x7Targets 0 + sample.targets 4 0 - seed := by
  simp only [CurvePublicSample.request, CurveGateRequest.retarget,
    CurveGateRequest.result, retargetBits, Fin.cases_zero]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (0 : Fin 5) ≠ 4),
    Function.update_of_ne (by decide : (1 : Fin 5) ≠ 4),
    Function.update_of_ne (by decide : (2 : Fin 5) ≠ 4),
    Function.update_of_ne (by decide : (3 : Fin 5) ≠ 4)]
  rw [fromBits_update_zero]
  ring

/-- A fresh free low target makes the actual pivot uniform. -/
theorem XPublicSample.pivot_uniform (sample : XPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype BaseField).map (fun seed =>
      (({sample with targets := (Function.update sample.targets 2
        (Function.update (sample.targets 2) 0 seed))} : XPublicSample).request.retarget
          input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  simp only [XPublicSample.pivot_seed]
  exact uniform_subtract_field _

/-- A fresh free low target makes the actual pivot uniform. -/
theorem YPublicSample.pivot_uniform (sample : YPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype BaseField).map (fun seed =>
      (({sample with targets := (Function.update sample.targets 2
        (Function.update (sample.targets 2) 1 seed))} : YPublicSample).request.retarget
          input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  simp only [YPublicSample.pivot_seed]
  rw [show (fun seed : BaseField =>
      (sample.request.retarget input target).x9Targets 0 + 2 * sample.targets 2 1 - 2 * seed) =
      (fun value : BaseField =>
        (sample.request.retarget input target).x9Targets 0 + 2 * sample.targets 2 1 - value) ∘
        (fun seed : BaseField => 2 * seed) from rfl,
    ← PMF.map_comp, uniform_scale_field 2 twoInverse twoInverse_cancel,
    uniform_subtract_field]

/-- A fresh free low target makes the actual pivot uniform. -/
theorem ZPublicSample.pivot_uniform (sample : ZPublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype BaseField).map (fun seed =>
      (({sample with targets := (Function.update sample.targets 2
        (Function.update (sample.targets 2) 0 seed))} : ZPublicSample).request.retarget
          input target).x9Targets 0) = PMF.uniformOfFintype BaseField := by
  simp only [ZPublicSample.pivot_seed]
  exact uniform_subtract_field _

/-- A fresh free low target makes the actual pivot uniform. -/
theorem CurvePublicSample.pivot_uniform (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) :
    (PMF.uniformOfFintype BaseField).map (fun seed =>
      (({sample with targets := (Function.update sample.targets 4
        (Function.update (sample.targets 4) 0 seed))} : CurvePublicSample).request.retarget
          input target).x7Targets 0) = PMF.uniformOfFintype BaseField := by
  simp only [CurvePublicSample.pivot_seed]
  exact uniform_subtract_field _

end

end Kriterion.ArgoMAC.Security
