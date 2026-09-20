import Proof.Privacy.Simulator.Arithmetic.EncLinkCanonicalSource
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSaved

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- Every accepted row stores a canonical widened label word. -/
theorem encLinkRowSamples_wide [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey secondKey label : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (key : memory.ram 40 = secondKey.setWidth 256)
    (selected : memory.ram (memory.ram 32) = label.setWidth 256)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support)
    (accepted : result.1.2.2 ≠ 7467) :
    result.1.1.ram (BitVec.ofNat 256 output) =
      ((result.1.1.ram (BitVec.ofNat 256 output)).setWidth 128).setWidth 256 := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have success : before.registers 7 ≠ 0#256 := fun failed => accepted ((encLinkAfterQuery_rejected before).mpr failed)
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  obtain ⟨value, encoded⟩ := internalForwardSamples_valueWitness attempts
    (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)) before spent
    (encLinkPhysicalIndex index).castSucc (state.permutations (encLinkPhysicalIndex index))
    (encLinkInput memory firstKey)
    ((encLinkPrepared_family memory index _ state ready.represented ready.capacity).permutations _)
    (encLinkPrepared_values memory index _).2.1
    (encLinkInput_operand state memory index indices suffix firstKey output limit ready)
    fit (ready.capacity.overlay _) member success
  change (encLinkAfterQuery before).1.ram _ = ((encLinkAfterQuery before).1.ram _ |>.setWidth 128).setWidth 256
  rw [encLinkRowQuery_output attempts state memory before spent index indices suffix firstKey output limit
    ready member success secondKey label key selected, encoded]
  have word : BitVec.ofNat 256 value.val = (blockFin.symm value).setWidth 256 := by
    apply BitVec.eq_of_toNat_eq
    simp [blockFin, BitVec.equivFin]
  rw [word]
  simp [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le]

/-- Every successful loop result stores canonical widened words throughout its output array. -/
theorem encLinkLoopSamples_wide [BN254.FieldCertificate]
    (attempts : Nat) (firstKey secondKey : Block) (x y : BitVec coordinateBitCount)
    (labels : Fin 508 → Block) (positions : List (Fin 508)) (position : Nat)
    (memory : Memory) (state : SparseOracleFamily) (suffix : List Bool) (inputBase output limit : Nat)
    (ready : EncLinkLoopMemory state memory (positions.map encLinkIndexAt) suffix firstKey output limit)
    (stored : EncLinkDataMemory memory position inputBase labels x y secondKey)
    (ordered : EncLinkConsecutive position positions) (remaining : position + positions.length = 508)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < positions.length →
      inputBase + inputOffset ≠ output + outputOffset)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix (positions.map encLinkIndexAt) memory state).support)
    (accepted : result.1.2.2 ≠ 7467) :
    ∀ offset, offset < positions.length → result.1.1.ram (BitVec.ofNat 256 (output + offset)) =
      ((result.1.1.ram (BitVec.ofNat 256 (output + offset))).setWidth 128).setWidth 256 := by
  induction positions generalizing position memory state output limit result with
  | nil => intro offset inside; simp at inside
  | cons head positions ih =>
      have headPosition := encLinkConsecutive_head position head positions ordered
      have current : EncLinkDataMemory memory head.val inputBase labels x y secondKey := by rw [headPosition]; exact stored
      obtain ⟨row, rowMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      change result ∈ (if row.1.2.2 = 7467 then PMF.pure row else
        (encLinkLoopSamples attempts firstKey suffix (positions.map encLinkIndexAt) row.1.1 row.2).map
          (encLinkCharge row.1.2.1)).support at member
      by_cases failed : row.1.2.2 = 7467
      · rw [if_pos failed] at member
        have same : result = row := by simpa using member
        exact False.elim (accepted (same ▸ failed))
      · rw [if_neg failed] at member
        obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have next := ((encLinkRowSamples_progress attempts state memory (encLinkIndexAt head)
          (positions.map encLinkIndexAt) suffix firstKey output limit ready row rowMember).resolve_left failed).1
        have nextData := encLinkRowSamples_data attempts state memory (encLinkIndexAt head)
          (positions.map encLinkIndexAt) suffix firstKey output limit ready head inputBase labels x y secondKey current
          (by simp only [List.length_map]; simp only [List.length_cons] at remaining; omega)
          inputLower inputUpper (fun offset inside => by simpa only [Nat.add_zero] using separate offset inside 0 (by simp))
          row rowMember failed
        have data : EncLinkDataMemory row.1.1 (position + 1) inputBase labels x y secondKey := by simpa only [headPosition] using nextData
        have nextSeparate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < positions.length →
            inputBase + inputOffset ≠ (output + 1) + outputOffset := by
          intro inputOffset inside outputOffset valid
          have distinct := separate inputOffset inside (outputOffset + 1) (by simpa using Nat.add_lt_add_right valid 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1 outputOffset] using distinct
        have tailWide := ih (position + 1) row.1.1 row.2 (output + 1) (limit + 1) next data
          (encLinkConsecutive_tail position head positions ordered)
          (by simp only [List.length_cons] at remaining; omega) nextSeparate tail tailMember accepted
        intro offset inside
        cases offset with
        | zero =>
            have kept := encLinkLoopSamples_beforeOutput attempts firstKey suffix (positions.map encLinkIndexAt)
              row.1.1 row.2 (output + 1) (limit + 1) output next ready.outputLower (Nat.lt_succ_self output) tail tailMember
            have wide := encLinkRowSamples_wide attempts state memory (encLinkIndexAt head)
              (positions.map encLinkIndexAt) suffix firstKey secondKey (labels head) output limit ready stored.whitening
              (encLinkDataMemory_selected memory head inputBase labels x y secondKey current) row rowMember failed
            simpa only [encLinkCharge, chargedResult, Nat.add_zero, kept] using wide
        | succ offset =>
            simpa only [encLinkCharge, chargedResult, Nat.add_assoc, Nat.add_comm 1 offset] using
              tailWide offset (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)

end Kriterion.ArgoMAC.ArithmeticSimulator
