import Proof.Privacy.Simulator.Arithmetic.EncLinkDataMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- The semantic coordinate invariant supplies the exact source row operand. -/
theorem encLinkDataMemory_input (memory : Memory) (position : Fin 508) (inputBase : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (firstKey secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey) :
    encLinkInput memory firstKey = blockFin (xor (encodeBit (encLinkBitAt x y position)) firstKey) := by
  unfold encLinkInput
  rw [stored.active, encLinkCoordinateWord_bit]
  rfl

/-- Every accepted source row preserves the complete semantic data invariant. -/
theorem encLinkRowSamples_data (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (position : Fin 508) (inputBase : Nat) (labels : Fin 508 → Block)
    (x y : BitVec coordinateBitCount) (secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey)
    (remaining : indices.length + 1 = 508 - position.val)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (separate : ∀ offset, offset < 508 → inputBase + offset ≠ output)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support)
    (accepted : result.1.2.2 ≠ 7467) :
    EncLinkDataMemory result.1.1 (position.val + 1) inputBase labels x y secondKey := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have success : before.registers 7 ≠ 0#256 := fun failed => accepted ((encLinkAfterQuery_rejected before).mpr failed)
  exact encLinkDataMemory_step attempts state memory before spent index indices suffix firstKey output limit ready
    member success position inputBase labels x y secondKey stored remaining inputLower inputUpper separate

/-- The stored row has the exact source query, selected label, and complete oracle-state distribution. -/
theorem encLinkRowSamples_dataSource [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (position : Fin 508) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit inputBase : Nat)
    (ready : EncLinkLoopMemory state memory (encLinkIndexAt position :: indices) suffix firstKey output limit)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey) :
    (encLinkRowSamples attempts state memory (encLinkIndexAt position)
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).map (encLinkRowValue output) =
      (drawCutoffLaw attempts ((state.permutations (encLinkPhysicalIndex (encLinkIndexAt position))).forward
        (blockFin (xor (encodeBit (encLinkBitAt x y position)) firstKey)))).map
          (Option.map fun result => encLinkMaskReply secondKey (labels position)
            (result.1, state.updatePermutation (encLinkPhysicalIndex (encLinkIndexAt position)) result.2)) := by
  have exactRow := encLinkRowSamples_source attempts state memory (encLinkIndexAt position) indices suffix firstKey
    output limit ready secondKey (labels position) stored.whitening
    (encLinkDataMemory_selected memory position inputBase labels x y secondKey stored)
  simpa only [encLinkDataMemory_input memory position inputBase labels x y firstKey secondKey stored] using exactRow

end Kriterion.ArgoMAC.ArithmeticSimulator
