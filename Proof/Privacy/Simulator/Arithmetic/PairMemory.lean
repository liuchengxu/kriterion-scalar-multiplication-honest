import Proof.Privacy.Simulator.Arithmetic.PairStore
import Proof.Privacy.Simulator.Arithmetic.SwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Distinct offsets select distinct cells within one word address cycle. -/
theorem wordOffset_ne (address : Word) (first second : Nat)
    (firstBound : first < 2 ^ 256) (secondBound : second < 2 ^ 256) (different : first ≠ second) :
    address + BitVec.ofNat 256 first ≠ address + BitVec.ofNat 256 second := by
  intro equal
  have canceled := add_left_cancel equal
  have values := congrArg BitVec.toNat canceled
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstBound,
    Nat.mod_eq_of_lt secondBound] at values
  exact different values

/-- RAM agreement on the stored cells preserves a pair-list representation. -/
theorem RepresentsPairs.congr (pairs : List (Word × Word)) (original updated : Word → Word)
    (address : Word) (represented : RepresentsPairs original address pairs)
    (same : ∀ index, index < 2 * pairs.length →
      updated (address + BitVec.ofNat 256 index) = original (address + BitVec.ofNat 256 index)) :
    RepresentsPairs updated address pairs := by
  induction pairs generalizing address with
  | nil => trivial
  | cons pair rest ih =>
      rcases represented with ⟨left, right, tail⟩
      refine ⟨?_, ?_, ?_⟩
      · have first := same 0 (by simp)
        simpa using first.trans (by simpa using left)
      · have second := same 1 (by simp; omega)
        simpa using second.trans (by simpa using right)
      · apply ih (address + 2#256) tail
        intro index bound
        have cell := same (index + 2) (by simp; omega)
        simpa [BitVec.ofNat_add, add_assoc, add_comm, add_left_comm] using cell

/-- A pair store prepends one entry without changing any later entry. -/
theorem pairStored_represents (memory : Memory) (pairs : List (Word × Word))
    (represented : RepresentsPairs memory.ram (memory.registers 9 + 2#256) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256) :
    RepresentsPairs (pairStored memory).ram (memory.registers 9)
      ((memory.registers 8, memory.registers 10) :: pairs) := by
  obtain ⟨left, right⟩ := pairStored_values memory
  refine ⟨left, right, ?_⟩
  apply RepresentsPairs.congr pairs memory.ram (pairStored memory).ram
    (memory.registers 9 + 2#256) represented
  intro index bound
  have offsetBound : index + 2 < 2 ^ 256 := by omega
  have first := wordOffset_ne (memory.registers 9) (index + 2) 0 offsetBound (by decide) (by omega)
  have second := wordOffset_ne (memory.registers 9) (index + 2) 1 offsetBound (by decide) (by omega)
  have regroup : memory.registers 9 + 2#256 + BitVec.ofNat 256 index =
      memory.registers 9 + BitVec.ofNat 256 (index + 2) := by
    simp [BitVec.ofNat_add, add_assoc, add_comm, add_left_comm]
  apply pairStored_other memory _
  · simpa [regroup] using first
  · simpa [regroup] using second

end Kriterion.ArgoMAC.ArithmeticSimulator
