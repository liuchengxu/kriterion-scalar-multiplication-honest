import Proof.Privacy.Simulator.Arithmetic.EncLinkArrayFrame
import Proof.Privacy.Simulator.Arithmetic.EncLinkCoordinateStep
import Proof.Privacy.Simulator.Arithmetic.EncLinkOrder

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The semantic invariant retains every selected source label and the exact coordinate words. -/
structure EncLinkDataMemory (memory : Memory) (position inputBase : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (secondKey : Block) : Prop where
  stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0
    (List.ofFn fun index => (labels index).setWidth 256)
  inputCursor : memory.ram 32 = BitVec.ofNat 256 (inputBase + position)
  active : memory.ram 35 = encLinkCoordinateWord (508 - position) x y
  saved : memory.ram 36 = y.setWidth 256
  whitening : memory.ram 40 = secondKey.setWidth 256

/-- The stored array gives the exact selected source label at the current input cursor. -/
theorem encLinkDataMemory_selected (memory : Memory) (position : Fin 508) (inputBase : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey) :
    memory.ram (memory.ram 32) = (labels position).setWidth 256 := by
  rw [stored.inputCursor]
  have value := stored.stored position.val (by rw [List.length_ofFn]; exact position.isLt)
  simpa only [Nat.zero_add, BitVec.ofNat_add, List.getElem_ofFn] using value

/-- Every accepted row retains the complete selected-label and coordinate invariant. -/
theorem encLinkDataMemory_step (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (accepted : before.registers 7 ≠ 0#256) (position : Fin 508) (inputBase : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey)
    (remaining : indices.length + 1 = 508 - position.val)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ offset, offset < 508 → inputBase + offset ≠ output) :
    EncLinkDataMemory (encLinkAfterQuery before).1 (position.val + 1) inputBase labels x y secondKey := by
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have kept := encLinkRowQuery_private attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output :=
    (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have safe : ∀ scratch : Nat, scratch < 256 → before.ram 33 ≠ BitVec.ofNat 256 scratch := by
    intro scratch small
    rw [cursor]
    exact encLinkOutput_separate output scratch ready.outputLower upper small
  have currentSafe : ∀ scratch : Nat, scratch < 256 → memory.ram 33 ≠ BitVec.ofNat 256 scratch := by
    intro scratch small
    rw [ready.cursor]
    exact encLinkOutput_separate output scratch ready.outputLower upper small
  have cursors := encLinkRowQuery_cursors attempts state memory before spent index (indices.flatMap encLinkIndexBits ++ suffix)
    ready.represented ready.capacity fit supported accepted (currentSafe 32 (by decide)) (currentSafe 38 (by decide))
  have coordinates := encLinkRowQuery_coordinateStep attempts state memory before spent index indices suffix firstKey output limit
    ready supported accepted x y (by rw [remaining]; exact stored.active) stored.saved (by omega)
  constructor
  · apply encLinkRowQuery_wordsAt attempts state memory before spent index indices suffix firstKey output limit
      ready supported inputBase 0 _ (by omega) _ _ stored.stored
    · simpa only [List.length_ofFn, Nat.add_zero] using inputUpper
    · intro offset inside
      exact separate offset (by simpa only [List.length_ofFn] using inside)
  · rw [cursors.1, stored.inputCursor, BitVec.ofNat_add]
    simp only [Nat.add_assoc, BitVec.ofNat_add, show (1 : Word) = 1#256 from rfl, BitVec.add_assoc]
  · rw [coordinates.1]
    congr 1
    have bound := position.isLt
    omega
  · exact coordinates.2
  · rw [encLinkAfterQuery_frame before 40 (safe 32 (by decide)) (safe 38 (by decide))
      (Ne.symm (safe 40 (by decide))) (by decide)]
    exact (kept 40 (by decide) (by decide) (by decide)).trans stored.whitening

end Kriterion.ArgoMAC.ArithmeticSimulator
