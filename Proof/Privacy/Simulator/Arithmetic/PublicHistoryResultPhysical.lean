import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The history header uses the fourth region of the selected physical oracle. -/
theorem historyHeader_address (memory : Memory) (oracle : Fin 15749)
    (header : memory.registers 6 = oracleAddress oracle 0 0) :
    historyHeader memory = oracleAddress oracle 3 0 := by
  simp [historyHeader, header, oracleAddress, oracleCell, BitVec.ofNat_add, Nat.add_assoc, add_assoc]

/-- The next history pair uses consecutive cells after the 256-cell header reserve. -/
theorem publicHistoryResult_addresses (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count) :
    historyHeader memory = oracleAddress oracle 3 0 ∧
    historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) =
      oracleAddress oracle 3 (256 + 2 * count) ∧
    historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) + 1#256 =
      oracleAddress oracle 3 (257 + 2 * count) := by
  have selected := historyHeader_address memory oracle header
  rw [selected, counter]
  constructor
  · rfl
  have cursor : oracleAddress oracle 3 0 + (BitVec.ofNat 256 count * 2#256 + 256#256) =
      oracleAddress oracle 3 (256 + 2 * count) := by
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, oracleAddress_add]
    congr 1
    omega
  constructor
  · exact cursor
  · rw [cursor]
    change oracleAddress oracle 3 (256 + 2 * count) + BitVec.ofNat 256 1 = _
    rw [oracleAddress_add]
    congr 1
    omega

/-- The physical history cells cannot overlap the saved reply. -/
theorem publicHistoryResult_physicalReply (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) :
    (publicHistoryResult memory).1.registers 8 = memory.registers 8 := by
  rcases publicHistoryResult_addresses memory oracle count header counter with ⟨selected, domain, range⟩
  apply publicHistoryResult_reply memory
  · rw [selected]
    exact oracleAddress_private_disjoint oracle 3 0 50 (by decide) (by decide)
  · rw [domain]
    exact oracleAddress_private_disjoint oracle 3 _ 50 (by omega) (by decide)
  · rw [range]
    exact oracleAddress_private_disjoint oracle 3 _ 50 capacity (by decide)

/-- The history update preserves every other public table region. -/
theorem publicHistoryResult_publicFrame (memory : Memory) (oracle other : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (region : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (separate : other ≠ oracle ∨ region ≠ 3) :
    (publicHistoryResult memory).1.ram (oracleAddress other region offset) =
      memory.ram (oracleAddress other region offset) := by
  rcases publicHistoryResult_addresses memory oracle count header counter with ⟨selected, domain, range⟩
  have headerSafe : historyHeader memory ≠ 50#256 := by
    rw [selected]
    exact oracleAddress_private_disjoint oracle 3 0 50 (by decide) (by decide)
  have scratchSafe := oracleAddress_private_disjoint other region offset 50 offsetFits (by decide)
  have apart : ∀ target, target < 2 ^ 110 →
      oracleAddress other region offset ≠ oracleAddress oracle 3 target := by
    intro target targetFits equal
    have eqs := oracleAddress_injective other oracle region 3 offset target offsetFits targetFits equal
    exact separate.elim (fun neq => neq eqs.1) (fun neq => neq eqs.2.1)
  rw [publicHistoryResult_ram memory headerSafe, range, domain, selected]
  split
  · rfl
  · split
    · simp [Function.update_of_ne, scratchSafe, apart 0 (by decide),
        apart (256 + 2 * count) (by omega), apart (257 + 2 * count) capacity]
    · rfl

/-- An accepted fixed query appends its visible ordered pair to the selected history. -/
theorem publicHistoryResult_historyPairs (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Word × Word)) (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (oracleAddress oracle 3 256) pairs)
    (capacity : 257 + 2 * pairs.length < 2 ^ 110)
    (accepted : memory.registers 7 ≠ 0#256)
    (fixed : memory.ram 49#256 = 0#256 ∨ memory.ram 49#256 = 1#256) :
    RepresentsPairs (publicHistoryResult memory).1.ram (oracleAddress oracle 3 256)
      (pairs ++ [(if memory.ram 49#256 = 0#256 then memory.ram 48 else memory.registers 8,
        if memory.ram 49#256 = 0#256 then memory.registers 8 else memory.ram 48)]) := by
  rcases publicHistoryResult_addresses memory oracle pairs.length header counter with ⟨selected, domain, range⟩
  have headerSafe : historyHeader memory ≠ 50#256 := by
    rw [selected]
    exact oracleAddress_private_disjoint oracle 3 0 50 (by decide) (by decide)
  let prepared : Memory := {
    memory with
    ram := Function.update memory.ram 50 (memory.registers 8)
    registers := Function.update (Function.update (Function.update memory.registers
      9 (oracleAddress oracle 3 256 + BitVec.ofNat 256 (2 * pairs.length)))
      8 (if memory.ram 49#256 = 0#256 then memory.ram 48 else memory.registers 8))
      10 (if memory.ram 49#256 = 0#256 then memory.registers 8 else memory.ram 48) }
  have retained : RepresentsPairs prepared.ram (oracleAddress oracle 3 256) pairs := by
    apply RepresentsPairs.congr pairs memory.ram prepared.ram _ represented
    intro index bound
    rw [oracleAddress_add]
    exact Function.update_of_ne (oracleAddress_private_disjoint oracle 3 _ 50 (by omega) (by decide)) _ _
  have stored := pairStored_appends prepared pairs (oracleAddress oracle 3 256)
    (by simp [prepared]) retained (by
      have : 2 ^ 110 < 2 ^ 256 := by decide
      omega)
  have values : prepared.registers 8 =
      (if memory.ram 49#256 = 0#256 then memory.ram 48 else memory.registers 8) ∧
      prepared.registers 10 =
      (if memory.ram 49#256 = 0#256 then memory.registers 8 else memory.ram 48) := by simp [prepared]
  rw [values.1, values.2] at stored
  apply RepresentsPairs.congr _ (pairStored prepared).ram _ _ stored
  intro index bound
  have headerApart : oracleAddress oracle 3 256 + BitVec.ofNat 256 index ≠ oracleAddress oracle 3 0 := by
    rw [oracleAddress_add]
    intro same
    have := (oracleAddress_injective oracle oracle 3 3 (256 + index) 0
      (by simp only [List.length_append, List.length_cons, List.length_nil] at bound; omega)
      (by decide) same).2.2
    omega
  rw [publicHistoryResult_ram memory headerSafe, if_neg accepted, if_pos fixed,
    range, domain, selected]
  rw [Function.update_of_ne headerApart]
  simp [prepared, pairStored, oracleAddress_add, add_assoc,
    show 256 + (2 * pairs.length + 1) = 257 + 2 * pairs.length by omega]

/-- An accepted fixed query increases its selected history count by one. -/
theorem publicHistoryResult_historyCount (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (accepted : memory.registers 7 ≠ 0#256)
    (fixed : memory.ram 49#256 = 0#256 ∨ memory.ram 49#256 = 1#256) :
    (publicHistoryResult memory).1.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 (count + 1) := by
  have selected := historyHeader_address memory oracle header
  have headerSafe : historyHeader memory ≠ 50#256 := by
    rw [selected]
    exact oracleAddress_private_disjoint oracle 3 0 50 (by decide) (by decide)
  rw [publicHistoryResult_ram memory headerSafe, if_neg accepted, if_pos fixed, selected,
    Function.update_self, counter, BitVec.ofNat_add]

end Kriterion.ArgoMAC.ArithmeticSimulator
