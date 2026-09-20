import Proof.Privacy.Simulator.Arithmetic.SparseMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sparse hash state stores its first-match pairs and its entry count. -/
structure HashMemory (ram : Word → Word) (oracle : Fin 15749) (pairs : List (Word × Word)) : Prop where
  count : ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 pairs.length
  stored : RepresentsPairs ram (oracleAddress oracle 0 (2 ^ 110 - 2 * pairs.length)) pairs

/-- The metadata loader preserves the hash header and every represented pair. -/
theorem HashMemory.loaded (memory : Memory) (oracle : Fin 15749) (pairs : List (Word × Word))
    (represented : HashMemory memory.ram oracle pairs) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    HashMemory (oracleLoaded memory).ram oracle pairs := by
  refine ⟨(oracleLoadRam_public memory oracle 0 0 (by decide)).trans represented.count, ?_⟩
  apply RepresentsPairs.congr pairs memory.ram _ _ represented.stored
  intro index bound
  rw [oracleAddress_add]
  exact oracleLoadRam_public memory oracle 0 _ (by omega)

/-- Fresh hash insertion preserves scratch and private RAM. -/
theorem hashInstalled_private (memory : Memory) (oracle : Fin 15749) (count cell : Nat)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (privateBound : cell < 2 ^ 96) :
    (hashInstalled memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have address : memory.registers 5 - 2#256 = oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1)) := by
    rw [base, oracleAddress_prepend oracle 0 count fits]
  have first := oracleAddress_private_disjoint oracle 0 (2 ^ 110 - 2 * (count + 1)) cell (by omega) privateBound
  have second := oracleAddress_private_disjoint oracle 0 (2 ^ 110 - 2 * (count + 1) + 1) cell (by omega) privateBound
  have advance : oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1)) + 1#256 =
      oracleAddress oracle 0 (2 ^ 110 - 2 * (count + 1) + 1) := oracleAddress_add oracle 0 _ 1
  simp only [hashInstalled, address, advance, Function.update_of_ne (Ne.symm second),
    Function.update_of_ne (Ne.symm first)]

/-- The count commit writes the selected header exactly. -/
theorem oracleCommitted_count (memory : Memory) :
    (oracleCommitted memory).ram (memory.ram 13) = memory.registers 0 := by
  simp [oracleCommitted]

/-- Hash insertion and count commit represent the complete first-match table update. -/
theorem hashInstalled_committed (memory : Memory) (oracle : Fin 15749) (pairs : List (Word × Word))
    (represented : RepresentsPairs memory.ram (oracleAddress oracle 0 (2 ^ 110 - 2 * pairs.length)) pairs)
    (base : memory.registers 5 = oracleAddress oracle 0 (2 ^ 110 - 2 * pairs.length))
    (count : memory.registers 4 = BitVec.ofNat 256 pairs.length)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (pairs.length + 1) + 256 < 2 ^ 110) :
    HashMemory (oracleCommitted (hashInstalled memory)).ram oracle
      ((memory.registers 8, memory.registers 0) :: pairs) := by
  have capacity : 2 * (pairs.length + 1) ≤ 2 ^ 110 := by omega
  have retained := hashInstalled_private memory oracle pairs.length 13 base capacity (by decide)
  have saved : (hashInstalled memory).ram 13 = oracleAddress oracle 0 0 := retained.trans header
  have cursor : (hashInstalled memory).registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * (pairs.length + 1)) := by
    simp only [show (hashInstalled memory).registers 1 = memory.registers 5 - 2#256 by simp [hashInstalled]]
    rw [base, oracleAddress_prepend oracle 0 pairs.length capacity]
  have installed := hashInstalled_represents memory pairs (by simpa only [base] using represented)
    (by
      have large : 2 ^ 110 < 2 ^ 256 := by decide
      omega)
  refine ⟨?_, ?_⟩
  · rw [← saved, oracleCommitted_count]
    simp [hashInstalled, count, BitVec.ofNat_add]
  · apply oracleCommitted_pairs (hashInstalled memory) _ _
      (by simpa only [cursor, List.length_cons] using installed)
    intro index bound
    rw [saved]
    exact descendingPairs_header_disjoint oracle 0 (pairs.length + 1) index fits (by simpa using bound)

/-- A known hash reply keeps every represented pair and commits the same count. -/
theorem hashFound_committed (memory : Memory) (oracle : Fin 15749) (pairs : List (Word × Word))
    (represented : HashMemory memory.ram oracle pairs)
    (count : memory.registers 0 = BitVec.ofNat 256 pairs.length)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * pairs.length + 256 < 2 ^ 110) :
    HashMemory (oracleCommitted (hashFound memory)).ram oracle pairs := by
  refine ⟨?_, ?_⟩
  · have saved : (hashFound memory).ram 13 = oracleAddress oracle 0 0 := header
    rw [← saved, oracleCommitted_count]
    simpa [hashFound] using count
  · apply oracleCommitted_pairs (hashFound memory) _ _ represented.stored
    intro index bound
    change _ ≠ memory.ram 13
    rw [header]
    exact descendingPairs_header_disjoint oracle 0 pairs.length index fits bound

end Kriterion.ArgoMAC.ArithmeticSimulator
