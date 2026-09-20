import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsLoop

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The natural-index point source matches the paper's correction point and free points. -/
def outputTargetPoint [BN254.FieldCertificate] [BN254.GroupCertificate]
    (output : BN254.Point) (free : Vector BN254.Point 90) (index : Nat) : BN254.Point :=
  if index = 0 then output - radix • pointHorner radix free.toList else (free.toList[index - 1]?).getD 0

/-- The natural-index scale source retains all 91 sampled scales. -/
def outputTargetScale [BN254.FieldCertificate] (scales : Fin 91 → BN254.NonZeroBase) (index : Nat) : BN254.NonZeroBase :=
  if inside : index < 91 then scales ⟨index, inside⟩ else ⟨1, one_ne_zero⟩

/-- The coordinate schedule agrees with vector order. -/
theorem homogeneousRowsWords_vector [BN254.FieldCertificate]
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (count : Nat) :
    homogeneousRowsWords points scales count = vectorWords homogeneousWords
      (Vector.ofFn fun i : Fin count => Security.homogeneousOfPoint (points i.val) (scales i.val)) := by
  have entries : (List.range count).map (fun index => Security.homogeneousOfPoint (points index) (scales index)) =
      (Vector.ofFn fun i : Fin count => Security.homogeneousOfPoint (points i.val) (scales i.val)).toList := by
    apply List.ext_getElem
    · simp
    · intro i first second
      simp
  rw [vectorWords, ← entries, List.flatMap_map]
  rfl

/-- The fixed point source equals each typed output-target point. -/
theorem outputTargetPoint_value [BN254.FieldCertificate] [BN254.GroupCertificate]
    (output : BN254.Point) (free : Vector BN254.Point 90) (i : Fin FieldMacToECMac.outputMacCount) :
    outputTargetPoint output free i.val =
      ((output - radix • pointHorner radix free.toList) :: free.toList)[i.val]'(by simpa using i.isLt) := by
  rcases i with ⟨i, inside⟩
  cases i with
  | zero => simp [outputTargetPoint]
  | succ i =>
      have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
      have valid : i < free.toList.length := by simp; omega
      simp [outputTargetPoint, Vector.get, List.getElem?_eq_getElem valid]

/-- Each positive row index selects the corresponding free point. -/
theorem outputTargetPoint_free [BN254.FieldCertificate] [BN254.GroupCertificate]
    (output : BN254.Point) (free : Vector BN254.Point 90) (i : Fin 90) :
    outputTargetPoint output free (i.val + 1) = free.get i := by
  simp [outputTargetPoint, Vector.get, List.getElem?_eq_getElem (by simpa using i.isLt : i.val < free.toList.length)]

/-- Each in-range scale index retains the sampled nonzero field value. -/
theorem outputTargetScale_value [BN254.FieldCertificate] (scales : Fin 91 → BN254.NonZeroBase) (i : Fin FieldMacToECMac.outputMacCount) :
    outputTargetScale scales i.val = scales i := by simp [outputTargetScale, i.isLt]

/-- The complete row-word source equals the original outputTargets definition. -/
theorem outputTargets_words [BN254.FieldCertificate] [BN254.GroupCertificate]
    (output : BN254.Point) (free : Vector BN254.Point 90) (scales : Fin 91 → BN254.NonZeroBase) :
    homogeneousRowsWords (outputTargetPoint output free) (outputTargetScale scales) 91 =
      vectorWords homogeneousWords (Security.outputTargets output free scales) := by
  rw [homogeneousRowsWords_vector]
  apply congrArg (vectorWords homogeneousWords)
  apply Vector.ext
  intro i inside
  simp only [Security.outputTargets, Vector.getElem_ofFn]
  have point := outputTargetPoint_value output free ⟨i, inside⟩
  simp only [Vector.get, Vector.getElem_mk, List.getElem_toArray] at *
  rw [point]
  simp [outputTargetScale, inside]

/-- A three-word source record supplies the exact canonical point encoding. -/
theorem storedPointEncoding_ofWordsAt [BN254.FieldCertificate] (ram : Word → Word) (pointer : Word) (start : Nat)
    (point : BN254.Point) (stored : WordsAt ram pointer start (pointWords point)) :
    StoredPointEncoding ram (pointer + BitVec.ofNat 256 start) point := by
  have zero := stored 0 (by rw [pointWords_length]; decide)
  have one := stored 1 (by rw [pointWords_length]; decide)
  have two := stored 2 (by rw [pointWords_length]; decide)
  simp only [Nat.add_zero] at zero
  have oneAddress : pointer + BitVec.ofNat 256 (start + 1) = pointer + BitVec.ofNat 256 start + 1 := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]; rfl
  have twoAddress : pointer + BitVec.ofNat 256 (start + 2) = pointer + BitVec.ofNat 256 start + 1 + 1 := by
    rw [BitVec.ofNat_add]; simp only [BitVec.add_assoc]; rfl
  rw [oneAddress] at one
  rw [twoAddress] at two
  cases point <;> simp_all [StoredPointEncoding, pointWords, writePoint, scalarAccumulator]

/-- The stored online source supplies every sampled point in canonical form. -/
theorem onlineWords_pointEncoding [BN254.FieldCertificate] (ram : Word → Word) (pointer : Word)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (stored : WordsAt ram pointer 0 (onlineWords sample)) (i : Fin 90) :
    StoredPointEncoding ram (pointer + 91 + BitVec.ofNat 256 (3 * i.val)) (sample.1 i) := by
  have after := wordsAt_append_right (show WordsAt ram pointer 0
    (onlineScaleSchedule.words (Vector.ofFn sample.2) ++ vectorWords pointWords (Vector.ofFn sample.1)) from stored)
  rw [onlineScaleSchedule.wordsLength, Nat.zero_add] at after
  have selected := wordsAt_vector pointWords 3 pointWords_length (Vector.ofFn sample.1) ram pointer 91 i after
  have encoded := storedPointEncoding_ofWordsAt ram pointer (91 + 3 * i.val) _ selected
  have address : pointer + BitVec.ofNat 256 (91 + 3 * i.val) = pointer + 91 + BitVec.ofNat 256 (3 * i.val) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  simpa [address] using encoded

private theorem scaleSchedule_word (scale : BN254.NonZeroBase) :
    scaleSchedule.words scale = [BitVec.ofNat 256 scale.value.val] := rfl

private theorem onlineScaleSchedule_words (values : Vector BN254.NonZeroBase 91) :
    onlineScaleSchedule.words values = vectorWords scaleSchedule.words values := rfl

/-- The stored online source supplies every sampled scale word. -/
theorem onlineWords_scale [BN254.FieldCertificate] (ram : Word → Word) (pointer : Word)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (stored : WordsAt ram pointer 0 (onlineWords sample)) (i : Fin FieldMacToECMac.outputMacCount) :
    ram (pointer + BitVec.ofNat 256 i.val) = BitVec.ofNat 256 (sample.2 i).value.val := by
  have before := wordsAt_append_left (show WordsAt ram pointer 0
    (onlineScaleSchedule.words (Vector.ofFn sample.2) ++ vectorWords pointWords (Vector.ofFn sample.1)) from stored)
  rw [onlineScaleSchedule_words] at before
  have selected := wordsAt_vector scaleSchedule.words 1 scaleSchedule.wordsLength (Vector.ofFn sample.2) ram pointer 0 i before
  have value := selected 0 (by rw [scaleSchedule.wordsLength]; decide)
  simpa only [scaleSchedule_word, List.getElem_cons_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, Vector.get_ofFn] using value

end Kriterion.ArgoMAC.ArithmeticSimulator
