import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- This equivalence separates the total from the free masks. -/
def fromBitsSplitEquiv (count : Nat) :
    (Fin (count + 1) → BaseField) ≃ BaseField × (Fin count → BaseField) where
  toFun values := (DigitAdaptor.fromBits values, fun index => values index.succ)
  invFun pair := Fin.cases (pair.1 - 2 * DigitAdaptor.fromBits pair.2) pair.2
  left_inv values := by
    funext index
    refine Fin.cases ?_ (fun _ => rfl) index
    simp only [Fin.cases_zero]
    rw [DigitAdaptor.fromBits, Fin.foldr_succ]
    simp [DigitAdaptor.fromBits]
  right_inv pair := by
    apply Prod.ext
    · dsimp
      rw [DigitAdaptor.fromBits, Fin.foldr_succ]
      simp [DigitAdaptor.fromBits]
    · rfl

/-- Uniform masks give a uniform total and independent uniform free masks. -/
theorem map_uniform_fromBitsSplit (count : Nat) :
    (PMF.uniformOfFintype (Fin (count + 1) → BaseField)).map (fromBitsSplitEquiv count) =
      PMF.uniformOfFintype (BaseField × (Fin count → BaseField)) :=
  map_uniformOfFintype_equivBetween (fromBitsSplitEquiv count)

/-- The total of uniform masks is uniform. -/
theorem map_uniform_fromBits (count : Nat) :
    (PMF.uniformOfFintype (Fin (count + 1) → BaseField)).map DigitAdaptor.fromBits =
      PMF.uniformOfFintype BaseField := by
  have h := congrArg (fun p => p.map Prod.fst) (map_uniform_fromBitsSplit count)
  simpa [PMF.map_comp, Function.comp_def, fromBitsSplitEquiv, map_uniform_prod_fst] using h

/-- The free masks keep their uniform distribution. -/
theorem map_uniform_maskTail (count : Nat) :
    (PMF.uniformOfFintype (Fin (count + 1) → BaseField)).map
        (fun values index => values index.succ) =
      PMF.uniformOfFintype (Fin count → BaseField) := by
  have h := congrArg (fun p => p.map Prod.snd) (map_uniform_fromBitsSplit count)
  simpa [PMF.map_comp, Function.comp_def, fromBitsSplitEquiv, map_uniform_prod_snd] using h

/-- Each free mask vector determines one vector with the specified total. -/
def fromBitsFiberEquiv (count : Nat) (target : BaseField) :
    (Fin count → BaseField) ≃ {values : Fin (count + 1) → BaseField |
      DigitAdaptor.fromBits values = target} where
  toFun tail := ⟨(fromBitsSplitEquiv count).symm (target, tail),
    congrArg Prod.fst ((fromBitsSplitEquiv count).apply_symm_apply (target, tail))⟩
  invFun values := fun index => values.1 index.succ
  left_inv _ := rfl
  right_inv values := by
    apply Subtype.ext
    have h := (fromBitsSplitEquiv count).symm_apply_apply values.1
    change (fromBitsSplitEquiv count).symm
      (DigitAdaptor.fromBits values.1, fun index => values.1 index.succ) = values.1 at h
    rw [values.2] at h
    exact h

/-- Retargeting uniform masks gives the uniform distribution on the target fiber. -/
theorem map_uniform_retargetBits (count : Nat) (target : BaseField) :
    letI : Nonempty {values : Fin (count + 1) → BaseField |
      DigitAdaptor.fromBits values = target} :=
        ⟨fromBitsFiberEquiv count target (fun _ => 0)⟩
    (PMF.uniformOfFintype (Fin (count + 1) → BaseField)).map
        (fun values => retargetBits values target) =
      (PMF.uniformOfFintype {values : Fin (count + 1) → BaseField |
        DigitAdaptor.fromBits values = target}).map Subtype.val := by
  classical
  letI : Nonempty {values : Fin (count + 1) → BaseField |
    DigitAdaptor.fromBits values = target} :=
      ⟨fromBitsFiberEquiv count target (fun _ => 0)⟩
  rw [← map_uniformOfFintype_equivBetween (fromBitsFiberEquiv count target),
    PMF.map_comp, ← map_uniform_maskTail count, PMF.map_comp]
  rfl

/-- This equivalence adds the selected slope to each field mask. -/
def maskShiftEquiv (slope input : BaseField) :
    (Fin coordinateBitCount → BaseField) ≃ (Fin coordinateBitCount → BaseField) where
  toFun values index := if coordinateValues input index then slope + values index else values index
  invFun values index := if coordinateValues input index then -slope + values index else values index
  left_inv values := by
    funext index
    cases selected : coordinateValues input index <;> simp [selected]
  right_inv values := by
    funext index
    cases selected : coordinateValues input index <;> simp [selected]

/-- The mask shift adds the slope times the input to the field total. -/
theorem fromBits_maskShift (slope input : BaseField)
    (values : Fin coordinateBitCount → BaseField) :
    DigitAdaptor.fromBits (maskShiftEquiv slope input values) =
      slope * input + DigitAdaptor.fromBits values := by
  change DigitAdaptor.fromBits
    (fun index => if coordinateValues input index then slope + values index else values index) = _
  rw [DigitAdaptor.fromBitsAffine, coordinateBitValue]

end

end Kriterion.ArgoMAC.Security
