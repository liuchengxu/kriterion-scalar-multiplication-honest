import Proof.Privacy.Simulator.Arithmetic.DrawMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The predicate records the exact RAM representation of a word list. -/
def WordsAt (ram : Word → Word) (pointer : Word) (start : Nat) (words : List Word) : Prop :=
  ∀ index (inside : index < words.length),
    ram (pointer + BitVec.ofNat 256 (start + index)) = words[index]

/-- The source writer establishes the exact word-list representation. -/
theorem wordsAt_store (pointer : Word) (start : Nat) (ram : Word → Word) (words : List Word)
    (fits : start + words.length ≤ 2 ^ 256) :
    WordsAt (storeDrawWords pointer start ram words) pointer start words := by
  intro index inside
  exact storeDrawWords_get pointer start ram words index inside fits

/-- A concatenated source retains its first word list at the same address. -/
theorem wordsAt_append_left {ram : Word → Word} {pointer : Word} {start : Nat}
    {first second : List Word} (stored : WordsAt ram pointer start (first ++ second)) :
    WordsAt ram pointer start first := by
  intro index inside
  have value := stored index (by simp; omega)
  simpa only [List.getElem_append_left inside] using value

/-- A concatenated source retains its second word list after the first. -/
theorem wordsAt_append_right {ram : Word → Word} {pointer : Word} {start : Nat}
    {first second : List Word} (stored : WordsAt ram pointer start (first ++ second)) :
    WordsAt ram pointer (start + first.length) second := by
  intro index inside
  have value := stored (first.length + index) (by simp; omega)
  simpa only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Nat.add_assoc] using value

/-- Each fixed-size record has its exact position in a concatenated list. -/
theorem wordsAt_flatMap {A : Type} (encode : A → List Word) (count : Nat)
    (size : ∀ value, (encode value).length = count) (entries : List A)
    (ram : Word → Word) (pointer : Word) (start row : Nat) (inside : row < entries.length)
    (stored : WordsAt ram pointer start (entries.flatMap encode)) :
    WordsAt ram pointer (start + count * row) (encode entries[row]) := by
  induction entries generalizing start row with
  | nil => simp at inside
  | cons head tail ih =>
      cases row with
      | zero =>
          simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using wordsAt_append_left stored
      | succ row =>
          have after := wordsAt_append_right stored
          rw [size] at after
          have selected := ih (start + count) row (by simpa using inside) after
          simpa only [List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc, Nat.add_comm count (count * row)] using selected

/-- Each sampled vector record has its exact position in RAM. -/
theorem wordsAt_vector {A : Type} {length : Nat} (encode : A → List Word) (count : Nat)
    (size : ∀ value, (encode value).length = count) (entries : Vector A length)
    (ram : Word → Word) (pointer : Word) (start : Nat) (row : Fin length)
    (stored : WordsAt ram pointer start (vectorWords encode entries)) :
    WordsAt ram pointer (start + count * row.val) (encode (entries.get row)) := by
  exact wordsAt_flatMap encode count size entries.toList ram pointer start row.val
    (by simpa using row.isLt) stored

end Kriterion.ArgoMAC.ArithmeticSimulator
