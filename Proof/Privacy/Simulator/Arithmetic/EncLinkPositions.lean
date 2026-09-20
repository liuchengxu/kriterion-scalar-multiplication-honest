import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography

/-- The first coordinate occupies the first 254 selected-label positions. -/
def encLinkXPosition (index : Fin coordinateBitCount) : Fin 508 := ⟨index.val, by have bound : index.val < 254 := index.isLt; omega⟩

/-- The second coordinate occupies the last 254 selected-label positions. -/
def encLinkYPosition (index : Fin coordinateBitCount) : Fin 508 := ⟨254 + index.val, by have bound : index.val < 254 := index.isLt; omega⟩

/-- The first position range selects the exact x oracle index. -/
theorem encLinkIndexAt_x (index : Fin coordinateBitCount) : encLinkIndexAt (encLinkXPosition index) = (.x, index) := by
  have bound : index.val < 254 := index.isLt
  unfold encLinkIndexAt encLinkXPosition
  dsimp only
  rw [dif_pos bound]

/-- The second position range selects the exact y oracle index. -/
theorem encLinkIndexAt_y (index : Fin coordinateBitCount) : encLinkIndexAt (encLinkYPosition index) = (.y, index) := by
  have bound : ¬254 + index.val < 254 := by omega
  simp only [encLinkIndexAt, encLinkYPosition, dif_neg bound, Nat.add_sub_cancel_left]

/-- The complete row list has the same order as the physical machine schedule. -/
theorem encLinkPositions_indices : (List.finRange 508).map encLinkIndexAt = encLinkIndices := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, encLinkIndices_length]
  · intro index left right
    simp only [List.getElem_map, List.getElem_finRange]
    exact (encLinkIndices_get ⟨index, by simpa only [List.length_map, List.length_finRange] using left⟩).symm

/-- The complete row list is consecutive from position zero. -/
theorem encLinkPositions_consecutive : EncLinkConsecutive 0 (List.finRange 508) := by
  intro index inside
  simp only [List.getElem_finRange, Nat.zero_add, Fin.val_cast]

/-- The complete row list contains the first coordinate before the second coordinate. -/
theorem encLinkPositions_split : List.finRange 508 = List.ofFn encLinkXPosition ++ List.ofFn encLinkYPosition := by
  apply List.ext_getElem
  · simp only [List.length_finRange, List.length_append, List.length_ofFn]; rfl
  · intro index left right
    simp only [List.getElem_finRange, List.getElem_append, List.length_ofFn]
    split
    · simp only [List.getElem_ofFn, encLinkXPosition]
      exact Fin.ext rfl
    · simp only [List.getElem_ofFn, encLinkYPosition]
      apply Fin.ext
      simp only [Fin.val_cast]
      change index = 254 + (index - 254)
      have : ¬index < 254 := by assumption
      omega

end Kriterion.ArgoMAC.ArithmeticSimulator
