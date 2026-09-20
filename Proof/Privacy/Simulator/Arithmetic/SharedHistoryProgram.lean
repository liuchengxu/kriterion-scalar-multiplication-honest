import Proof.Privacy.Simulator.Arithmetic.SharedHistorySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- A selected append and the other history frames implement the exact metadata update. -/
theorem SharedHistoryMemory.program (original updated : Word → Word) (metadata : Metadata)
    (command : SharedCommand) (represented : SharedHistoryMemory original metadata)
    (selected : HistoryMemory updated (sharedPhysicalIndex (.inl command.1)).castSucc
      (recordHistoryPairs metadata.fixedTranscript command.1 ++ [(historyWord command.2.1, historyWord command.2.2)]))
    (fits : ∀ index, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript index).length < 2 ^ 110)
    (others : ∀ index : Shared.FixedKeyIndex, index ≠ command.1 → ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 3 offset) =
        original (oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 3 offset)) :
    SharedHistoryMemory updated (metadata.program command) := by
  intro index
  change HistoryMemory updated _ (recordHistoryPairs
    (PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2 :: metadata.fixedTranscript) index)
  rw [recordHistoryPairs_cons]
  by_cases same : index = command.1
  · subst index
    simp only [if_pos rfl]
    exact selected
  · simp only [show command.1 ≠ index from Ne.symm same, ↓reduceIte]
    exact HistoryMemory.congr original updated _ _ (represented index) (fits index) (others index same)

/-- Distinct named fixed indices have distinct physical history regions. -/
theorem sharedFixedPhysical_ne {first second : Shared.FixedKeyIndex} (different : first ≠ second) :
    (sharedPhysicalIndex (.inl first)).castSucc ≠ (sharedPhysicalIndex (.inl second)).castSucc := by
  intro equal
  exact different (Sum.inl.inj (sharedPhysicalIndex.injective (Fin.castSucc_injective _ equal)))

end
end Kriterion.ArgoMAC.ArithmeticSimulator
