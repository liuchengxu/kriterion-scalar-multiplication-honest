import Proof.Privacy.Simulator.Arithmetic.PointHornerLoop
import Proof.Privacy.Simulator.Arithmetic.DrawMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A flat point list has three words per point. -/
theorem pointListWords_length [BN254.FieldCertificate] (points : List BN254.Point) :
    (points.flatMap pointWords).length = 3 * points.length := by
  induction points with
  | nil => rfl
  | cons point points ih => simp [ih, pointWords_length, Nat.mul_add, Nat.add_comm]

/-- Each flat point entry has its exact canonical coordinate words. -/
theorem pointListWords_get [BN254.FieldCertificate] (points : List BN254.Point) (i : Nat) (inside : i < points.length)
    (offset : Nat) (small : offset < 3) :
    (points.flatMap pointWords)[3 * i + offset]'(by rw [pointListWords_length]; omega) =
      (pointWords points[i])[offset]'(by rw [pointWords_length]; exact small) := by
  induction points generalizing i with
  | nil => simp at inside
  | cons head tail ih =>
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
          exact List.getElem_append_left (by rw [pointWords_length]; exact small)
      | succ i =>
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem_append_right (by rw [pointWords_length]; omega)]
          simp only [pointWords_length]
          have position : 3 * (i + 1) + offset - 3 = 3 * i + offset := by omega
          simpa only [position] using ih i (by simpa using inside)

/-- The RAM source writer gives the exact canonical point at every point index. -/
theorem storedPoint_drawWords [BN254.FieldCertificate] (pointer : Word) (start : Nat)
    (ram : Word → Word) (points : List BN254.Point) (i : Nat) (inside : i < points.length)
    (fits : start + 3 * points.length ≤ 2 ^ 256) :
    storedPoint (storeDrawWords pointer start ram (points.flatMap pointWords))
      (pointer + BitVec.ofNat 256 (start + 3 * i)) = some points[i] := by
  have getWord (offset : Nat) (small : offset < 3) :
      storeDrawWords pointer start ram (points.flatMap pointWords)
        (pointer + BitVec.ofNat 256 (start + 3 * i + offset)) =
      (pointWords points[i])[offset]'(by rw [pointWords_length]; exact small) := by
    rw [show start + 3 * i + offset = start + (3 * i + offset) by omega,
      storeDrawWords_get pointer start ram (points.flatMap pointWords) (3 * i + offset)
        (by rw [pointListWords_length]; omega) (by rw [pointListWords_length]; exact fits)]
    exact pointListWords_get points i inside offset small
  have zero := getWord 0 (by decide)
  have one := getWord 1 (by decide)
  have two := getWord 2 (by decide)
  simp only [Nat.add_zero] at zero
  rw [BitVec.ofNat_add (start + 3 * i) 1, ← BitVec.add_assoc] at one
  have addressTwo : pointer + BitVec.ofNat 256 (start + 3 * i + 2) =
      pointer + BitVec.ofNat 256 (start + 3 * i) + 1 + 1 := by
    rw [BitVec.ofNat_add]; simp only [BitVec.add_assoc]; rfl
  rw [addressTwo] at two
  apply Eq.trans _ (scalarMultiple_write (fun _ => 0) points[i])
  apply readPoint_congr <;>
    cases point : points[i] <;>
    simp_all [storedPoint, scalarMultiple, writePoint, pointWords]

/-- Each online point has its exact sampled value at the point-region pointer. -/
theorem onlineWords_point [BN254.FieldCertificate] (pointer : Word) (ram : Word → Word)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) (i : Fin 90) :
    storedPoint (storeDrawWords pointer 0 ram (onlineWords sample))
      (pointer + 91 + BitVec.ofNat 256 (3 * i.val)) = some (sample.1 i) := by
  rw [onlineWords, storeDrawWords_append, onlineScaleSchedule.wordsLength]
  simp only [Nat.zero_add, vectorWords]
  have source := storedPoint_drawWords pointer 91
    (storeDrawWords pointer 0 ram (onlineScaleSchedule.words (Vector.ofFn sample.2)))
    (Vector.ofFn sample.1).toList i.val (by simp [i.isLt]) (by simp)
  have address : pointer + BitVec.ofNat 256 (91 + 3 * i.val) =
      pointer + 91 + BitVec.ofNat 256 (3 * i.val) := by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  simpa only [address, Vector.getElem_toList, Vector.getElem_ofFn] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
