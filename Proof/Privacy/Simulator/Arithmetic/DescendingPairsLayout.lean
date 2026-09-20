import Proof.Privacy.Simulator.Arithmetic.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.InstallFreshState

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Adding an offset retains the canonical address in the same table region. -/
theorem oracleAddress_add (oracle : Fin 15749) (table : Fin 4) (start offset : Nat) :
    oracleAddress oracle table start + BitVec.ofNat 256 offset =
      oracleAddress oracle table (start + offset) := by
  simp [oracleAddress, oracleCell, BitVec.ofNat_add, add_assoc]

/-- A descending table base subtracts exactly two cells per stored pair. -/
theorem oracleAddress_descending (oracle : Fin 15749) (table : Fin 4) (count : Nat)
    (fits : 2 * count ≤ 2 ^ 110) :
    oracleAddress oracle table (2 ^ 110) - BitVec.ofNat 256 (2 * count) =
      oracleAddress oracle table (2 ^ 110 - 2 * count) := by
  apply sub_eq_iff_eq_add.mpr
  rw [oracleAddress_add]
  congr 1
  omega

/-- Different table regions have disjoint descending pair cells. -/
theorem descendingPairs_disjoint (oracle : Fin 15749) (left right : Fin 4)
    (different : left ≠ right) (leftCount rightCount : Nat)
    (leftFits : 2 * leftCount ≤ 2 ^ 110) (rightFits : 2 * rightCount ≤ 2 ^ 110)
    (first second : Nat) (firstFits : first < 2 * leftCount) (secondFits : second < 2 * rightCount) :
    oracleAddress oracle left (2 ^ 110 - 2 * leftCount) + BitVec.ofNat 256 first ≠
      oracleAddress oracle right (2 ^ 110 - 2 * rightCount) + BitVec.ofNat 256 second := by
  rw [oracleAddress_add, oracleAddress_add]
  intro equal
  exact different (oracleAddress_injective oracle oracle left right _ _ (by omega) (by omega) equal).2.1

/-- Every occupied descending cell lies above the temporary RAM cells. -/
theorem descendingPairs_safe (oracle : Fin 15749) (table : Fin 4) (count index : Nat)
    (fits : 2 * count ≤ 2 ^ 110) (inside : index < 2 * count) :
    8 ≤ (oracleAddress oracle table (2 ^ 110 - 2 * count) + BitVec.ofNat 256 index).toNat := by
  rw [oracleAddress_add, oracleAddress_value oracle table _ (by omega)]
  have lower := (oracleCell_bounds oracle table (2 ^ 110 - 2 * count + index) (by omega)).1
  exact le_trans (by decide : 8 ≤ 2 ^ 128) lower

/-- The loader computes the descending input base from the persistent count. -/
theorem oracleLoaded_inputBase (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (stored : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * count ≤ 2 ^ 110) :
    (oracleLoaded memory).registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count) := by
  have header := oracleLoadRam_header memory oracle index
  rw [index, oracleHeader_address] at header
  simp only [oracleLoaded, Function.update_of_ne (by decide : (1 : Register) ≠ 15),
    Function.update_of_ne (by decide : (1 : Register) ≠ 7), Function.update_of_ne (by decide : (1 : Register) ≠ 6),
    Function.update_of_ne (by decide : (1 : Register) ≠ 5), Function.update_of_ne (by decide : (1 : Register) ≠ 4),
    Function.update_of_ne (by decide : (1 : Register) ≠ 3), Function.update_of_ne (by decide : (1 : Register) ≠ 2),
    Function.update_self, index, oracleHeader_address, header, stored]
  rw [← BitVec.ofNat_mul, show count * 2 = 2 * count by omega,
    oracleAddress_add, Nat.zero_add, oracleAddress_descending oracle 0 count fits]

/-- The output table starts one region after the input table. -/
theorem oracleAddress_next_table (oracle : Fin 15749) (offset : Nat) :
    oracleAddress oracle 0 offset + BitVec.ofNat 256 (2 ^ 110) = oracleAddress oracle 1 offset := by
  simp [oracleAddress, oracleCell, BitVec.ofNat_add, add_assoc, add_comm, add_left_comm]

/-- The loader computes the descending output base from the same persistent count. -/
theorem oracleLoaded_outputBase (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (stored : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * count ≤ 2 ^ 110) :
    (oracleLoaded memory).registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count) := by
  have relation : (oracleLoaded memory).registers 3 =
      (oracleLoaded memory).registers 1 + BitVec.ofNat 256 (2 ^ 110) := by simp [oracleLoaded]
  rw [relation, oracleLoaded_inputBase memory oracle count index stored fits, oracleAddress_next_table]

end Kriterion.ArgoMAC.ArithmeticSimulator
