import Proof.Privacy.Simulator.Arithmetic.EncLinkRead

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The low-bit mask is the widened source bit encoding. -/
theorem encLink_lowBit (word : Word) :
    word &&& 1#256 = (encodeBit (word.getLsbD 0)).setWidth 256 := by
  rw [BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases word.getLsbD 0 <;> rfl

/-- The shifted coordinate exposes the selected source bit. -/
theorem encLink_shiftBit (coordinate : BitVec coordinateBitCount) (index : Fin coordinateBitCount) :
    (coordinate.setWidth 256 >>> index.val).getLsbD 0 = coordinate.getLsb index := by
  have bound : index.val < 256 := by have := index.isLt; change index.val < 254 at this; omega
  have fits : coordinate.toNat < 2 ^ 256 := lt_trans coordinate.isLt (by decide)
  simp [BitVec.getLsbD_setWidth, BitVec.getLsb, bound, BitVec.getElem_eq_testBit_toNat, Nat.mod_eq_of_lt fits]
  change (coordinate.toNat % 2 ^ 256).testBit index.val = _
  rw [Nat.mod_eq_of_lt fits]

/-- The query operand is the source Even-Mansour input for the selected bit. -/
theorem encLinkPrepared_sourceOperand (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (coordinate : BitVec coordinateBitCount) (keys : WhiteningKeys)
    (bits : memory.ram (35 : Word) = coordinate.setWidth 256 >>> index.2.val)
    (first : memory.ram (39 : Word) = keys.first.setWidth 256) :
    (encLinkPrepared memory index rest).registers 8 =
      (xor (encodeBit (coordinate.getLsb index.2)) keys.first).setWidth 256 := by
  rw [(encLinkPrepared_values memory index rest).1, bits, first, encLink_lowBit, encLink_shiftBit]
  exact BitVec.setWidth_xor.symm

/-- The accepted label result is exactly the source EncPRF transform. -/
theorem encLinkFinish_transformAt (memory : Memory)
    (oracle : PermutationOracle EncPRF.PermutationIndex Block) (keys : WhiteningKeys)
    (counter : EncPRF.Counter) (label : Block)
    (reply : memory.registers 8 =
      ((oracle.permutation (counter.coordinate, counter.index))
        (xor (encodeBit counter.bit) keys.first)).setWidth 256)
    (second : memory.ram (40 : Word) = keys.second.setWidth 256)
    (selected : memory.ram (41 : Word) = label.setWidth 256) :
    (executeLinear encLinkFinish memory).registers 8 =
      (EncPRF.transformAt oracle keys counter label).setWidth 256 := by
  rw [encLinkFinish_value, reply, second, selected]
  simp only [EncPRF.transformAt, EncPRF.evenMansourPad, evenMansour, encrypt, Cryptography.xor,
    BitVec.setWidth_xor]

end Kriterion.ArgoMAC.ArithmeticSimulator
