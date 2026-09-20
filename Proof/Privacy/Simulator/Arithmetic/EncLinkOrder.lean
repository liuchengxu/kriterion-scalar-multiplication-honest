import Proof.Privacy.Simulator.Arithmetic.EncLinkCoordinate
import Proof.Privacy.Simulator.Arithmetic.EncLinkPhysicalIndex

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The schedule position selects one exact coordinate and source bit index. -/
def encLinkIndexAt (position : Fin 508) : EncPRF.PermutationIndex :=
  if first : position.val < 254 then (.x, ⟨position.val, first⟩)
  else (.y, ⟨position.val - 254, by have := position.isLt; change position.val - 254 < 254; omega⟩)

/-- The fixed index prelude has the exact x-then-y source order. -/
theorem encLinkIndices_get (position : Fin 508) :
    encLinkIndices[position.val]'(by rw [encLinkIndices_length]; exact position.isLt) = encLinkIndexAt position := by
  unfold encLinkIndices encLinkIndexAt
  simp only [List.getElem_append, List.length_map, List.length_finRange]
  by_cases first : position.val < 254
  · simp only [show coordinateBitCount = 254 from rfl, first, dite_true,
      List.getElem_map, List.getElem_finRange]
    exact congrArg (Prod.mk EncPRF.Coordinate.x) (Fin.ext rfl)
  · simp only [show coordinateBitCount = 254 from rfl, first, dite_false,
      List.getElem_map, List.getElem_finRange, List.length_map, List.length_finRange]
    exact congrArg (Prod.mk EncPRF.Coordinate.y) (Fin.ext rfl)


/-- The active word exposes the source bit at the current schedule position. -/
theorem encLinkCoordinateWord_bit (position : Fin 508) (x y : BitVec coordinateBitCount) :
    (encLinkCoordinateWord (508 - position.val) x y).getLsbD 0 =
      match (encLinkIndexAt position).1 with
      | .x => x.getLsb (encLinkIndexAt position).2
      | .y => y.getLsb (encLinkIndexAt position).2 := by
  have bound := position.isLt
  by_cases first : position.val < 254
  · have remaining : 254 < 508 - position.val := by omega
    have shift : 508 - (508 - position.val) = position.val := by omega
    simp only [encLinkCoordinateWord, if_pos remaining, shift, encLinkIndexAt, dif_pos first]
    exact encLink_shiftBit x ⟨position.val, first⟩
  · have remaining : ¬254 < 508 - position.val := by omega
    have shift : 254 - (508 - position.val) = position.val - 254 := by omega
    simp only [encLinkCoordinateWord, if_neg remaining, shift, encLinkIndexAt, dif_neg first]
    exact encLink_shiftBit y ⟨position.val - 254, by change position.val - 254 < 254; omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
