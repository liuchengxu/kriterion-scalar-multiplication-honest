import Proof.Privacy.Simulator.Arithmetic.EncLinkTypedOutput
import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsCoordinate
import Proof.Privacy.Simulator.Arithmetic.WordsAt

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] EncPRF.transformAt

/-- The complete transformed word array determines the typed input MAC. -/
theorem encLinkOutputMac_transform (memory : Memory) (output : Nat)
    (oracle : PermutationOracle EncPRF.PermutationIndex Block) (keys : WhiteningKeys)
    (input : BitInput) (mac : InputMac)
    (words : WordsAt memory.ram (BitVec.ofNat 256 output) 0
      ((List.finRange 508).map fun position =>
        (EncPRF.transformAt oracle keys
          ⟨(encLinkIndexAt position).1, (encLinkIndexAt position).2,
            encLinkBitAt input.xBits input.yBits position⟩ (encLinkMacLabels mac position)).setWidth 256)) :
    encLinkOutputMac memory output = EncPRF.transformMac oracle keys input mac := by
  have row (position : Fin 508) : memory.ram (BitVec.ofNat 256 (output + position.val)) =
      (EncPRF.transformAt oracle keys
        ⟨(encLinkIndexAt position).1, (encLinkIndexAt position).2,
          encLinkBitAt input.xBits input.yBits position⟩ (encLinkMacLabels mac position)).setWidth 256 := by
    have found := words position.val (by simpa using position.isLt)
    simpa only [List.getElem_map, List.getElem_finRange, Nat.zero_add, ← BitVec.ofNat_add, Fin.cast_mk, Fin.eta] using found
  change InputMac.mk _ _ = InputMac.mk _ _
  apply congrArg₂ InputMac.mk
  · apply Vector.ext
    intro index valid
    have found := row (encLinkXPosition ⟨index, valid⟩)
    simp only [EncPRF.transformCoordinateMac, Vector.getElem_ofFn]
    rw [show memory.ram (BitVec.ofNat 256 (output + index)) = _ from found]
    simp [encLinkBitAt, encLinkMacLabels, encLinkIndexAt_x, BitVec.setWidth_setWidth_of_le]
  · apply Vector.ext
    intro index valid
    have found := row (encLinkYPosition ⟨index, valid⟩)
    simp only [encLinkBitAt, encLinkMacLabels, encLinkIndexAt_y] at found
    simp only [EncPRF.transformCoordinateMac, Vector.getElem_ofFn]
    rw [show memory.ram (BitVec.ofNat 256 (output + 254 + index)) = _ from (by simpa only [encLinkYPosition, Nat.add_assoc] using found)]
    simp [BitVec.setWidth_setWidth_of_le]

end Kriterion.ArgoMAC.ArithmeticSimulator
