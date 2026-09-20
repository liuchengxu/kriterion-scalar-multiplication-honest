import Proof.Privacy.Simulator.Arithmetic.EncLinkInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Every accepted row retains the loop invariant for the remaining fixed schedule. -/
theorem encLinkInvariant_step [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory before : Memory) (spent : Nat)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (input : Fin (2 ^ 128))
    (operand : (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8 =
      BitVec.ofNat 256 input.val)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (accepted : before.registers 7 ≠ 0#256) :
    EncLinkLoopMemory
      (state.updatePermutation (encLinkPhysicalIndex index)
        (internalForwardMemoryState (state.permutations (encLinkPhysicalIndex index)) input before))
      (encLinkAfterQuery before).1 indices suffix firstKey (output + 1) (limit + 1) := by
  let oracle := encLinkPhysicalIndex index
  let rest := indices.flatMap encLinkIndexBits ++ suffix
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110 := by
    dsimp only [oracle]; omega
  have kept := encLinkRowQuery_private attempts state memory before spent index rest
    ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output :=
    (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have safe : ∀ scratch : Nat, scratch < 256 → before.ram 33 ≠ BitVec.ofNat 256 scratch := by
    intro scratch small
    rw [cursor]
    exact encLinkOutput_separate output scratch ready.outputLower upper small
  have inputSafe : memory.ram 33#256 ≠ 32#256 := by
    change memory.ram 33 ≠ BitVec.ofNat 256 32
    rw [ready.cursor]
    exact encLinkOutput_separate output 32 ready.outputLower upper (by decide)
  have countSafe : memory.ram 33#256 ≠ 38#256 := by
    change memory.ram 33 ≠ BitVec.ofNat 256 38
    rw [ready.cursor]
    exact encLinkOutput_separate output 38 ready.outputLower upper (by decide)
  have cursors := encLinkRowQuery_cursors attempts state memory before spent index rest
    ready.represented ready.capacity fit supported accepted inputSafe countSafe
  have nextFits := internalForwardFamily_fits state oracle input before ready.capacity fit
  have prepared := encLinkPrepared_family memory index rest state ready.represented ready.capacity
  have family := internalForwardSamples_family attempts (encLinkPrepared memory index rest) before spent
    state oracle input prepared ready.capacity (encLinkPrepared_values memory index rest).2.1 operand room supported
  constructor
  · apply encLinkAfterQuery_family before _ family nextFits
    · rw [cursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans upper (by decide))]
      exact upper
    · exact safe 32 (by decide)
    · exact safe 38 (by decide)
  · exact nextFits
  · exact internalForwardFamily_count state oracle input before limit ready.baseCount
  · intro current
    exact le_trans (internalForwardFamily_overlayCount state oracle input before limit
      ready.overlayCount current) (Nat.le_succ limit)
  · have available := ready.room
    simp only [List.length_cons] at available
    omega
  · rw [cursors.2.2, ready.counter, List.length_cons, BitVec.ofNat_add]
    simp
  · rw [cursors.2.1, ready.cursor, BitVec.ofNat_add]
    rfl
  · exact le_trans ready.outputLower (Nat.le_succ output)
  · have available := ready.outputUpper
    simp only [List.length_cons] at available
    omega
  · rw [encLinkAfterQuery_frame before 39 (safe 32 (by decide)) (safe 38 (by decide))
      (Ne.symm (safe 39 (by decide))) (by decide)]
    exact (kept 39 (by decide) (by decide) (by decide)).trans ready.whitening
  · rw [encLinkAfterQuery_bits, internalForwardSamples_bits _ _ _ _ before spent supported]
    exact (encLinkPrepared_values memory index rest).2.2.2.2

end Kriterion.ArgoMAC.ArithmeticSimulator
