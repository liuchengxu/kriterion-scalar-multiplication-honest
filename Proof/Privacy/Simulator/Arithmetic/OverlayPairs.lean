import Proof.Privacy.Simulator.Arithmetic.OverlayMetadata
import Proof.Privacy.Simulator.Arithmetic.PairMemory
import Proof.Privacy.Simulator.Arithmetic.ReversePairs

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A pair store appends one entry without changing the previous entries. -/
theorem pairStored_appends (memory : Memory) (pairs : List (Word × Word)) (address : Word)
    (cursor : memory.registers 9 = address + BitVec.ofNat 256 (2 * pairs.length))
    (represented : RepresentsPairs memory.ram address pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256) :
    RepresentsPairs (pairStored memory).ram address
      (pairs ++ [(memory.registers 8, memory.registers 10)]) := by
  apply (RepresentsPairs.append pairs _ _ _).mpr
  constructor
  · apply RepresentsPairs.congr pairs memory.ram (pairStored memory).ram address represented
    intro index bound
    apply pairStored_other
    · rw [cursor]
      exact wordOffset_ne address index (2 * pairs.length) (by omega) (by omega) (by omega)
    · rw [cursor]
      have next : address + BitVec.ofNat 256 (2 * pairs.length) + 1#256 =
          address + BitVec.ofNat 256 (2 * pairs.length + 1) := by
        simp [BitVec.ofNat_add, add_assoc]
      rw [next]
      exact wordOffset_ne address index (2 * pairs.length + 1) (by omega) (by omega) (by omega)
  · rw [← cursor]
    obtain ⟨left, right⟩ := pairStored_values memory
    exact ⟨left, right, trivial⟩

/-- The append setup selects the first free pair after the represented overlay. -/
theorem overlayAppendReady_cursor (memory : Memory) (pairs : List (Word × Word))
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 pairs.length) :
    (overlayAppendReady memory).registers 9 =
      overlayHeader memory + 256#256 + BitVec.ofNat 256 (2 * pairs.length) := by
  simp [overlayAppendReady, counter, ← BitVec.ofNat_mul, Nat.mul_comm,
    add_assoc, add_comm, add_left_comm]

/-- The append block represents the source overlay with one final swap. -/
theorem overlayAppended_represents (memory : Memory) (pairs : List (Word × Word))
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (overlayHeader memory + 256#256) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256)
    (headerSafe : ∀ index, index < 2 * (pairs.length + 1) →
      overlayHeader memory + 256#256 + BitVec.ofNat 256 index ≠ overlayHeader memory) :
    RepresentsPairs (overlayAppended memory).ram (overlayHeader memory + 256#256)
      (pairs ++ [(memory.registers 8, memory.ram 14)]) := by
  have stored := pairStored_appends (overlayAppendReady memory) pairs
    (overlayHeader memory + 256#256) (overlayAppendReady_cursor memory pairs counter) represented fits
  have values : (overlayAppendReady memory).registers 8 = memory.registers 8 ∧
      (overlayAppendReady memory).registers 10 = memory.ram 14 := by simp [overlayAppendReady]
  rw [values.1, values.2] at stored
  apply RepresentsPairs.congr _ _ _ _ stored
  intro index bound
  have safe := headerSafe index (by simpa using bound)
  simp [overlayAppended, overlayAppendFinished, pairStored, overlayAppendReady, safe]

/-- The append block increments the overlay header by one. -/
theorem overlayAppended_count (memory : Memory) :
    (overlayAppended memory).ram (overlayHeader memory) = memory.ram (overlayHeader memory) + 1#256 := by
  simp [overlayAppended, overlayAppendFinished, pairStored, overlayAppendReady]

end Kriterion.ArgoMAC.ArithmeticSimulator
