import Proof.Privacy.Simulator.Arithmetic.EncLinkSchedule
import Proof.Privacy.Simulator.Arithmetic.HashOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The high half of a packed hash word is its first widened source block. -/
theorem encLink_hashHigh (word : Word) :
    word >>> 128 = (Security.SimulatorMachine.hashFin.symm word.toFin).1.setWidth 256 := by
  rw [hashFin_decode]
  apply BitVec.eq_of_toNat_eq
  have high : word.toNat / 2 ^ 128 < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    simpa only [show 2 ^ 128 * 2 ^ 128 = 2 ^ 256 by norm_num] using word.isLt
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt high]
  exact Nat.shiftRight_eq_div_pow _ _

/-- The low mask of a packed hash word is its second widened source block. -/
theorem encLink_hashLow (word : Word) :
    word &&& BitVec.ofNat 256 (2 ^ 128 - 1) =
      (Security.SimulatorMachine.hashFin.symm word.toFin).2.setWidth 256 := by
  rw [hashFin_decode]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide)]
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : 2 ^ 128 - 1 < 2 ^ 256), Nat.and_two_pow_sub_one_eq_mod]

/-- The scheduled key cells contain the exact source hash pair in paper order. -/
theorem encLinkScheduled_keys (memory : Memory) :
    let keys := Security.SimulatorMachine.hashFin.symm (memory.registers 8).toFin
    (encLinkScheduled memory).ram (39 : Word) = keys.1.setWidth 256 ∧
    (encLinkScheduled memory).ram (40 : Word) = keys.2.setWidth 256 := by
  dsimp only
  rw [(encLinkScheduled_memory memory).1]
  simp only [Function.update_self, Function.update_of_ne (by decide : (39 : Word) ≠ 40)]
  exact ⟨encLink_hashHigh _, encLink_hashLow _⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
