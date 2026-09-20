import Proof.Privacy.Simulator.Arithmetic.RecordedPublicWord

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- A complete accepted forward query records its exact typed public pair. -/
theorem storedForwardSamples_fixedHistory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (input output : Block) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram (sharedPhysicalIndex (.inl index)).castSucc state)
    (histories : SharedHistoryMemory memory.ram metadata)
    (selected : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl index)).val)
    (operand : memory.registers 8 = historyWord input)
    (savedInput : memory.ram 48#256 = historyWord input) (savedTag : memory.ram 49#256 = 0#256)
    (room : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayRoom : 256 + 2 * state.overlay.length < 2 ^ 110)
    (historyRoom : ∀ current, 257 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.base.used memory).support)
    (reply : publicForwardReplyValue (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index input)
      state.overlay.length final = some output) :
    SharedHistoryMemory (recordedPublicForwardTail state.overlay.length final).1.ram
      (metadata.record (.fixedForward index input) output) := by
  have accepted : final.registers 7 ≠ 0#256 := by
    intro rejected
    simp [publicForwardReplyValue, rejected] at reply
  have small : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110 := by
    intro current
    have := historyRoom current
    omega
  have retained := storedForwardSamples_sharedHistory attempts state.base.used memory final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc metadata histories selected represented.base.count room small
  have frame := storedForwardSamples_historyFrame attempts state.base.used memory final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc selected represented.base.count room
  have saved48 := storedForwardSamples_private attempts state.base.used memory final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc 48 (by decide) (by decide) selected represented.base.count room
  have saved49 := storedForwardSamples_private attempts state.base.used memory final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc 49 (by decide) (by decide) selected represented.base.count room
  change final.ram 48#256 = memory.ram 48#256 at saved48
  change final.ram 49#256 = memory.ram 49#256 at saved49
  have scan := overlayForward_data state.overlay.length final
  obtain ⟨value, valueWord⟩ := programmedForwardSamples_valueWitness attempts memory final cost (sharedPhysicalIndex (.inl index)).castSucc state input.toFin
    represented selected operand room overlayRoom supported accepted
  have parsed : BitVec.ofNat 128 (BitVec.ofNat 256 value.val).toNat = output := by
    apply Option.some.inj
    simpa only [publicForwardReplyValue, if_neg accepted, publicAnswerValue, valueWord, PublicQuery.Answer] using reply
  have fullReply : (overlayForwardScan state.overlay.length final).1.registers 8 = historyWord output :=
    valueWord.trans ((historyWord_parsed value).symm.trans (congrArg historyWord parsed))
  unfold recordedPublicForwardTail
  rw [if_neg accepted, wordOutput_ram]
  apply publicHistoryResult_sharedForward _ metadata index input output
  · rw [scan.1]
    exact retained
  · exact (scan.2.2 6 (by decide)).trans frame.1
  · rw [scan.2.2 7 (by decide)]
    exact accepted
  · exact (congrFun scan.1 _).trans (saved49.trans savedTag)
  · exact (congrFun scan.1 _).trans (saved48.trans savedInput)
  · exact fullReply
  · exact historyRoom

/-- A complete accepted inverse query records its pair in forward orientation. -/
theorem storedInverseSamples_fixedHistory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (input output : Block) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram (sharedPhysicalIndex (.inl index)).castSucc state)
    (histories : SharedHistoryMemory memory.ram metadata)
    (selected : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl index)).val)
    (operand : memory.registers 8 = historyWord output)
    (savedInput : memory.ram 48#256 = historyWord output) (savedTag : memory.ram 49#256 = 1#256)
    (room : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayRoom : 256 + 2 * state.overlay.length < 2 ^ 110)
    (historyRoom : ∀ current, 257 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts state.base.used
      (publicInversePrepared state.overlay.length memory)).support)
    (reply : publicReplyValue (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index output)
      final = some input) :
    SharedHistoryMemory (recordedPublicInverseTail final).1.ram
      (metadata.record (.fixedInverse index output) input) := by
  have accepted : final.registers 7 ≠ 0#256 := by
    intro rejected
    simp [publicReplyValue, rejected] at reply
  have small : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110 := by
    intro current
    have := historyRoom current
    omega
  have preparedIndex := (publicInversePrepared_data state.overlay.length memory).2.trans selected
  have preparedCount := (publicInversePrepared_public state.overlay.length memory (sharedPhysicalIndex (.inl index)).castSucc 0 0 (by decide)).trans represented.base.count
  have preparedHistory := publicInversePrepared_sharedHistory state.overlay.length memory metadata histories small
  have retained := storedInverseSamples_sharedHistory attempts state.base.used _ final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc metadata preparedHistory preparedIndex preparedCount room small
  have header := storedInverseSamples_header attempts state.base.used _ final cost supported
    (sharedPhysicalIndex (.inl index)).castSucc preparedIndex preparedCount room
  have privateFrame (cell : Nat) (lower : 16 ≤ cell) (bound : cell < 2 ^ 96) :
      final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
    rw [storedInverseSamples_private attempts state.base.used _ final cost supported
      (sharedPhysicalIndex (.inl index)).castSucc cell lower bound preparedIndex preparedCount room, (publicInversePrepared_data state.overlay.length memory).1]
    exact oracleLoadRam_private memory cell lower bound
  have saved48 : final.ram 48#256 = historyWord output := (privateFrame 48 (by decide) (by decide)).trans savedInput
  have saved49 : final.ram 49#256 = 1#256 := (privateFrame 49 (by decide) (by decide)).trans savedTag
  obtain ⟨value, valueWord⟩ := programmedInverseSamples_valueWitness attempts memory final cost (sharedPhysicalIndex (.inl index)).castSucc state output.toFin
    represented selected operand (by omega) overlayRoom supported accepted
  have parsed : BitVec.ofNat 128 (BitVec.ofNat 256 value.val).toNat = input := by
    apply Option.some.inj
    simpa only [publicReplyValue, if_neg accepted, publicAnswerValue, valueWord, PublicQuery.Answer] using reply
  have fullReply : final.registers 8 = historyWord input :=
    valueWord.trans ((historyWord_parsed value).symm.trans (congrArg historyWord parsed))
  unfold recordedPublicInverseTail
  rw [if_neg accepted, wordOutput_ram]
  exact publicHistoryResult_sharedInverse final metadata index input output retained header accepted
    saved49 saved48 fullReply historyRoom

end
end Kriterion.ArgoMAC.ArithmeticSimulator
