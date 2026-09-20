import Proof.Privacy.Simulator.Arithmetic.SamplerBatchSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Distinct source indices select distinct RAM words. -/
theorem drawAddress_injective (pointer : Word) (first second : Nat)
    (firstFits : first < 2 ^ 256) (secondFits : second < 2 ^ 256) :
    pointer + BitVec.ofNat 256 first = pointer + BitVec.ofNat 256 second ↔ first = second := by
  constructor
  · intro equal
    have words := add_left_cancel equal
    have values := congrArg BitVec.toNat words
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt secondFits] using values
  · rintro rfl
    rfl

/-- The source writer preserves each cell outside its index range. -/
theorem storeDrawWords_outside (pointer : Word) (index : Nat) (ram : Word → Word)
    (words : List Word) (query : Nat) (fits : index + words.length ≤ 2 ^ 256)
    (queryFits : query < 2 ^ 256) (outside : query < index ∨ index + words.length ≤ query) :
    storeDrawWords pointer index ram words (pointer + BitVec.ofNat 256 query) =
      ram (pointer + BitVec.ofNat 256 query) := by
  induction words generalizing index ram with
  | nil => rfl
  | cons head tail ih =>
      have indexFits : index < 2 ^ 256 := by simp only [List.length_cons] at fits; omega
      have different : pointer + BitVec.ofNat 256 query ≠ pointer + BitVec.ofNat 256 index := by
        intro equal
        have same := (drawAddress_injective pointer query index queryFits indexFits).mp equal
        simp only [List.length_cons] at outside
        omega
      rw [storeDrawWords, ih (index + 1) _ (by simp only [List.length_cons] at fits; omega) (by
        simp only [List.length_cons] at outside; omega), Function.update_of_ne different]

/-- Every stored source word appears at its exact index. -/
theorem storeDrawWords_get (pointer : Word) (index : Nat) (ram : Word → Word)
    (words : List Word) (offset : Nat) (inside : offset < words.length)
    (fits : index + words.length ≤ 2 ^ 256) :
    storeDrawWords pointer index ram words (pointer + BitVec.ofNat 256 (index + offset)) =
      words[offset] := by
  induction words generalizing index ram offset with
  | nil => simp at inside
  | cons head tail ih =>
      cases offset with
      | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero, storeDrawWords]
          rw [storeDrawWords_outside pointer (index + 1) _ tail index
            (by simp only [List.length_cons] at fits; omega)
            (by simp only [List.length_cons] at fits; omega) (Or.inl (by omega))]
          simp
      | succ offset =>
          have bound : offset < tail.length := by simpa using inside
          have room : index + 1 + tail.length ≤ 2 ^ 256 := by
            simp only [List.length_cons] at fits; omega
          simpa only [storeDrawWords, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 offset] using
            ih (index + 1) (Function.update ram (pointer + BitVec.ofNat 256 index) head) offset bound room

end Kriterion.ArgoMAC.ArithmeticSimulator
