import Proof.Privacy.Simulator.Arithmetic.WordsAt

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sequential writer preserves every address outside its written cells. -/
theorem storeDrawWords_disjoint (pointer : Word) (start : Nat) (ram : Word → Word) (words : List Word)
    (query : Word) (separate : ∀ offset, offset < words.length → query ≠ pointer + BitVec.ofNat 256 (start + offset)) :
    storeDrawWords pointer start ram words query = ram query := by
  induction words generalizing start ram with
  | nil => rfl
  | cons word words ih =>
      rw [storeDrawWords, ih]
      · exact Function.update_of_ne (by simpa using separate 0 (by simp)) _ _
      · intro offset inside
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using separate (offset + 1) (by simpa using inside)

/-- Disjoint sequential writes preserve an exact RAM source list. -/
theorem wordsAt_store_disjoint (sourcePointer destination : Word) (sourceStart destinationStart : Nat)
    (ram : Word → Word) (source words : List Word)
    (stored : WordsAt ram sourcePointer sourceStart source)
    (separate : ∀ i, i < source.length → ∀ j, j < words.length →
      sourcePointer + BitVec.ofNat 256 (sourceStart + i) ≠ destination + BitVec.ofNat 256 (destinationStart + j)) :
    WordsAt (storeDrawWords destination destinationStart ram words) sourcePointer sourceStart source := by
  intro i inside
  rw [storeDrawWords_disjoint destination destinationStart ram words _ (separate i inside)]
  exact stored i inside

end Kriterion.ArgoMAC.ArithmeticSimulator
