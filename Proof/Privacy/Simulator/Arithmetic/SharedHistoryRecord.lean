import Proof.Privacy.Simulator.Arithmetic.SharedHistoryProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- The selected external pair and every other history frame retain the exact fixed transcript. -/
theorem SharedHistoryMemory.recordFixed (original updated : Word → Word) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (input output : Block) (direction : PermutationAction)
    (represented : SharedHistoryMemory original metadata)
    (selected : HistoryMemory updated (sharedPhysicalIndex (.inl index)).castSucc
      (recordHistoryPairs metadata.fixedTranscript index ++ [(historyWord input, historyWord output)]))
    (fits : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110)
    (others : ∀ current : Shared.FixedKeyIndex, current ≠ index → ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress (sharedPhysicalIndex (.inl current)).castSucc 3 offset) =
        original (oracleAddress (sharedPhysicalIndex (.inl current)).castSucc 3 offset)) :
    SharedHistoryMemory updated {metadata with fixedTranscript := (PermutationRecord.mk direction .adversary index input output :: metadata.fixedTranscript)} := by
  intro current
  change HistoryMemory updated _ (recordHistoryPairs
    (PermutationRecord.mk direction .adversary index input output :: metadata.fixedTranscript) current)
  rw [recordHistoryPairs_cons]
  by_cases same : current = index
  · subst current
    simp only [if_pos rfl]
    exact selected
  · simp only [show index ≠ current from Ne.symm same, ↓reduceIte]
    exact HistoryMemory.congr original updated _ _ (represented current) (fits current) (others current same)

/-- A frame over every fixed history retains any update that leaves the fixed transcript unchanged. -/
theorem SharedHistoryMemory.fixedFrame (original updated : Word → Word) (before after : Metadata)
    (represented : SharedHistoryMemory original before)
    (same : after.fixedTranscript = before.fixedTranscript)
    (fits : ∀ index, 256 + 2 * (recordHistoryPairs before.fixedTranscript index).length < 2 ^ 110)
    (frame : ∀ index : Shared.FixedKeyIndex, ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 3 offset) =
        original (oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 3 offset)) :
    SharedHistoryMemory updated after := by
  intro index
  change HistoryMemory updated _ (recordHistoryPairs after.fixedTranscript index)
  rw [same]
  exact HistoryMemory.congr original updated _ _ (represented index) (fits index) (frame index)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
