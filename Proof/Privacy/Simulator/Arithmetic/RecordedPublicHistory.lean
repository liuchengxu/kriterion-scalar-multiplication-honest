import Proof.Privacy.Simulator.Arithmetic.SharedHistoryRecord
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicPrivate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- Canonical input decoding preserves every fixed-key history. -/
theorem recordedPublicInputMemory_sharedHistory (memory : Memory) (metadata : Metadata)
    (request : SharedQuery) (rest : List Bool) (represented : SharedHistoryMemory memory.ram metadata)
    (room : ∀ index, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript index).length < 2 ^ 110) :
    SharedHistoryMemory (recordedPublicInputMemory memory request rest).ram metadata := by
  apply SharedHistoryMemory.fixedFrame memory.ram _ metadata metadata represented rfl room
  intro index offset bound
  exact recordedPublicInputMemory_public memory request rest _ 3 offset bound

/-- Inverse preparation preserves every fixed-key history. -/
theorem publicInversePrepared_sharedHistory (count : Nat) (memory : Memory) (metadata : Metadata)
    (represented : SharedHistoryMemory memory.ram metadata)
    (room : ∀ index, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript index).length < 2 ^ 110) :
    SharedHistoryMemory (publicInversePrepared count memory).ram metadata := by
  apply SharedHistoryMemory.fixedFrame memory.ram _ metadata metadata represented rfl room
  intro index offset bound
  exact publicInversePrepared_public count memory _ 3 offset bound

/-- A hash write preserves every fixed-key history region. -/
theorem hashHandlerSamples_sharedHistory (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support)
    (metadata : Metadata) (represented : SharedHistoryMemory memory.ram metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 15748)
    (counter : memory.ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory final.ram metadata := by
  apply SharedHistoryMemory.fixedFrame memory.ram final.ram metadata metadata represented rfl historyRoom
  intro current offset bound
  exact hashHandlerSamples_otherOracle count memory final cost supported 15748 _
    (permutationIndex_ne_hash _) 3 offset bound index counter room

/-- The raw forward query retains every fixed-key transcript before the public append. -/
theorem storedForwardSamples_sharedHistory (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (metadata : Metadata) (represented : SharedHistoryMemory memory.ram metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory final.ram metadata := by
  apply SharedHistoryMemory.fixedFrame memory.ram final.ram metadata metadata represented rfl historyRoom
  intro current offset bound
  by_cases same : (sharedPhysicalIndex (.inl current)).castSucc = oracle
  · rw [same]
    exact (storedForwardSamples_historyFrame attempts count memory final cost supported oracle index counter room).2 offset bound
  · exact storedForwardSamples_otherOracle attempts count memory final cost supported oracle _ same
      3 offset bound index counter room

/-- The raw inverse query retains every fixed-key transcript before the public append. -/
theorem storedInverseSamples_sharedHistory (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle : Fin 15749) (metadata : Metadata) (represented : SharedHistoryMemory memory.ram metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory final.ram metadata := by
  apply SharedHistoryMemory.fixedFrame memory.ram final.ram metadata metadata represented rfl historyRoom
  intro current offset bound
  by_cases same : (sharedPhysicalIndex (.inl current)).castSucc = oracle
  · rw [same]
    exact storedInverseSamples_historyFrame attempts count memory final cost supported oracle index counter room offset bound
  · exact storedInverseSamples_otherOracle attempts count memory final cost supported oracle _ same
      3 offset bound index counter room

/-- A successful forward public append records the visible ordered pair. -/
theorem publicHistoryResult_sharedForward (memory : Memory) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (input output : Block)
    (represented : SharedHistoryMemory memory.ram metadata)
    (header : memory.registers 6 = oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 0 0)
    (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 0#256)
    (operand : memory.ram 48#256 = historyWord input) (reply : memory.registers 8 = historyWord output)
    (room : ∀ current, 257 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory (publicHistoryResult memory).1.ram (metadata.record (.fixedForward index input) output) := by
  apply SharedHistoryMemory.recordFixed memory.ram _ metadata index input output .forward represented
  · have selected := publicHistoryResult_historyMemory memory _ _ (represented index) header (room index)
      accepted (Or.inl tag)
    have operandNat : memory.ram 48 = historyWord input := operand
    simpa only [tag, if_true, operand, operandNat, reply] using selected
  · intro current
    have := room current
    omega
  · intro current separate offset bound
    exact publicHistoryResult_publicFrame memory _ _ _ header (represented index).count (room index)
      3 offset bound (Or.inl (sharedFixedPhysical_ne separate))

/-- A successful inverse public append records the pair in forward orientation. -/
theorem publicHistoryResult_sharedInverse (memory : Memory) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (input output : Block)
    (represented : SharedHistoryMemory memory.ram metadata)
    (header : memory.registers 6 = oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 0 0)
    (accepted : memory.registers 7 ≠ 0#256) (tag : memory.ram 49#256 = 1#256)
    (operand : memory.ram 48#256 = historyWord output) (reply : memory.registers 8 = historyWord input)
    (room : ∀ current, 257 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory (publicHistoryResult memory).1.ram (metadata.record (.fixedInverse index output) input) := by
  apply SharedHistoryMemory.recordFixed memory.ram _ metadata index input output .inverse represented
  · have selected := publicHistoryResult_historyMemory memory _ _ (represented index) header (room index)
      accepted (Or.inr tag)
    have operandNat : memory.ram 48 = historyWord output := operand
    simpa only [tag, show (1#256 : Word) ≠ 0#256 from by decide, if_false, operand, operandNat, reply] using selected
  · intro current
    have := room current
    omega
  · intro current separate offset bound
    exact publicHistoryResult_publicFrame memory _ _ _ header (represented index).count (room index)
      3 offset bound (Or.inl (sharedFixedPhysical_ne separate))

/-- An encryption query leaves all histories and the answer unchanged. -/
theorem publicHistoryResult_nonfixed (memory : Memory)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256) :
    (publicHistoryResult memory).1.ram = memory.ram ∧
      (publicHistoryResult memory).1.registers 8 = memory.registers 8 := by
  unfold publicHistoryResult
  split
  · exact ⟨rfl, rfl⟩
  · simp only [if_neg forward, if_neg inverse]
    exact ⟨rfl, rfl⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
