import Proof.Privacy.Simulator.Arithmetic.EncLinkSelected

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The remaining count identifies the exact unconsumed coordinate bits. -/
def encLinkCoordinateWord (remaining : Nat) (x y : BitVec coordinateBitCount) : Word :=
  if 254 < remaining then x.setWidth 256 >>> (508 - remaining)
  else y.setWidth 256 >>> (254 - remaining)

/-- The shift and the single coordinate switch preserve the remaining bit sequence. -/
theorem encLinkCoordinateWord_step (remaining : Nat) (x y : BitVec coordinateBitCount)
    (positive : 0 < remaining) (bound : remaining ≤ 508) :
    (if remaining - 1 = 254 then y.setWidth 256 else encLinkCoordinateWord remaining x y >>> 1) =
      encLinkCoordinateWord (remaining - 1) x y := by
  by_cases boundary : remaining - 1 = 254
  · have current : remaining = 255 := by omega
    subst remaining
    simp [encLinkCoordinateWord]
  · by_cases first : 254 < remaining
    · have next : 254 < remaining - 1 := by omega
      have shift : 508 - (remaining - 1) = (508 - remaining) + 1 := by omega
      simp only [if_neg boundary, encLinkCoordinateWord, if_pos first, if_pos next, shift, BitVec.shiftRight_add]
    · have next : ¬254 < remaining - 1 := by omega
      have shift : 254 - (remaining - 1) = (254 - remaining) + 1 := by omega
      simp only [if_neg boundary, encLinkCoordinateWord, if_neg first, if_neg next, shift, BitVec.shiftRight_add]

/-- The accepted tail preserves the saved y coordinate and changes only the active bits. -/
theorem encLinkAfterQuery_coordinate (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256)
    (separate : memory.ram 33 ≠ 32 ∧ memory.ram 33 ≠ 35 ∧ memory.ram 33 ≠ 36 ∧ memory.ram 33 ≠ 38) :
    (encLinkAfterQuery memory).1.ram 35 =
      (if memory.ram 38 - 1 = 254#256 then memory.ram 36 else memory.ram 35) ∧
    (encLinkAfterQuery memory).1.ram 36 = memory.ram 36 := by
  rw [encLinkAfterQuery_ram memory accepted separate.1 separate.2.2.2]
  split <;> simp only [Function.update_apply, show (35 : Word) ≠ 38 from by decide,
    show (35 : Word) ≠ 32 from by decide, show (35 : Word) ≠ 33 from by decide,
    show (36 : Word) ≠ 38 from by decide, show (36 : Word) ≠ 32 from by decide,
    show (36 : Word) ≠ 33 from by decide, show (36 : Word) ≠ 35 from by decide,
    Ne.symm separate.2.1, Ne.symm separate.2.2.1, if_false, if_true, and_self]

end Kriterion.ArgoMAC.ArithmeticSimulator
