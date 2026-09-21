import Proof.Privacy.Simulator.Arithmetic.RecordedPublicSampleMemory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicOtherFamily
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFixedHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- Every typed successful handler reply retains its exact fixed-key transcript. -/
theorem recordedPublicHandlerSamples_history [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SharedOracleSource) (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (history : SharedHistoryMemory memory.ram state.metadata)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (historyRoom : ∀ current, 257 + 2 * (recordHistoryPairs state.metadata.fixedTranscript current).length < 2 ^ 110)
    (empty : memory.bits 3 = [])
    (stable : RecordedPublicReplyStable (publicHandlerKind request) attempts
      (publicSourceCount state request) (publicSourceOverlay state request) (recordedPublicInputMemory memory request rest))
    (result : Configuration 1810 × Nat) (reply : SharedAnswer request)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts (publicSourceCount state request)
      (publicSourceOverlay state request) memory request rest).support)
    (answered : answer request (result.1.memory.bits 3) = some reply) :
    SharedHistoryMemory result.1.memory.ram (state.metadata.record request reply) := by
  have stored := recordedPublicInputMemory_family memory request rest state.family represented capacity
  have values := recordedPublicInputMemory_values memory request rest
  have saved := recordedPublicInputMemory_saved memory request rest
  have outputEmpty := (recordedPublicInputMemory_output memory request rest).trans empty
  have past := recordedPublicInputMemory_sharedHistory memory state.metadata request rest history
    (fun current => by have := historyRoom current; omega)
  cases request with
  | fixedForward index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      let initial := recordedPublicInputMemory memory (.fixedForward index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_forwardMemory attempts
        (publicSourceCount state (.fixedForward index value)) (publicSourceOverlay state (.fixedForward index value)) memory (.fixedForward index value) rest rfl result supported
      have typed := recordedPublicForwardTail_answer (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value)
        (by intro key; simp) (state.family.permutations oracle).overlay.length raw.1
        ((congrFun (storedForwardSamples_bits attempts _ initial raw.1 raw.2 member) 3).trans outputEmpty)
        (stable raw member)
      have observed : publicForwardReplyValue (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value)
          (state.family.permutations oracle).overlay.length raw.1 = some reply := typed.symm.trans (memoryEq ▸ answered)
      have retained := storedForwardSamples_fixedHistory attempts initial raw.1 raw.2 state.metadata index value reply
        (state.family.permutations oracle) (stored.permutations oracle) past indexWord values.1 saved.1 saved.2
        (by have := room oracle; omega) (capacity.overlay oracle) historyRoom member observed
      rw [memoryEq]
      exact retained
  | encForward index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      let initial := recordedPublicInputMemory memory (.encForward index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_forwardMemory attempts
        (publicSourceCount state (.encForward index value)) (publicSourceOverlay state (.encForward index value)) memory (.encForward index value) rest rfl result supported
      change raw ∈ (storedForwardSamples attempts (state.family.permutations oracle).base.used initial).support at member
      change result.1.memory = (recordedPublicForwardTail (state.family.permutations oracle).overlay.length raw.1).1 at memoryEq
      have tag : initial.ram 49#256 = 2#256 := saved.2
      have retained := storedForwardSamples_sharedHistory attempts _ initial raw.1 raw.2 member oracle.castSucc
        state.metadata past indexWord (stored.permutations oracle).base.count (by have := room oracle; omega)
        (fun current => by have := historyRoom current; omega)
      have kept := storedForwardSamples_private attempts _ initial raw.1 raw.2 member oracle.castSucc 49 (by decide) (by decide)
        indexWord (stored.permutations oracle).base.count (by have := room oracle; omega)
      have ram := recordedPublicForwardTail_nonfixedRam (state.family.permutations oracle).overlay.length raw.1
        (by rw [kept, tag]; decide) (by rw [kept, tag]; decide)
      rw [memoryEq, ram]
      exact SharedHistoryMemory.fixedFrame raw.1.ram raw.1.ram state.metadata
        (state.metadata.record (.encForward index value) reply) retained rfl
        (fun current => by have := historyRoom current; omega) (by intros; rfl)
  | fixedInverse index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      let initial := recordedPublicInputMemory memory (.fixedInverse index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_inverseMemory attempts
        (publicSourceCount state (.fixedInverse index value)) (publicSourceOverlay state (.fixedInverse index value)) memory (.fixedInverse index value) rest rfl result supported
      have typed := recordedPublicInverseTail_answer (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value)
        (by intro key; simp) raw.1
        ((congrFun (storedInverseSamples_bits attempts _ _ raw.1 raw.2 member) 3).trans
          ((congrFun (publicInversePrepared_bits _ initial) 3).trans outputEmpty)) (stable raw member)
      have observed : publicReplyValue (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value)
          raw.1 = some reply := typed.symm.trans (memoryEq ▸ answered)
      have retained := storedInverseSamples_fixedHistory attempts initial raw.1 raw.2 state.metadata index reply value
        (state.family.permutations oracle) (stored.permutations oracle) past indexWord values.1 saved.1 saved.2
        (by have := room oracle; omega) (capacity.overlay oracle) historyRoom member observed
      rw [memoryEq]
      exact retained
  | encInverse index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      let initial := recordedPublicInputMemory memory (.encInverse index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_inverseMemory attempts
        (publicSourceCount state (.encInverse index value)) (publicSourceOverlay state (.encInverse index value)) memory (.encInverse index value) rest rfl result supported
      change raw ∈ (storedInverseSamples attempts (state.family.permutations oracle).base.used
        (publicInversePrepared (state.family.permutations oracle).overlay.length initial)).support at member
      have tag : initial.ram 49#256 = 3#256 := saved.2
      have preparedIndex := (publicInversePrepared_data (state.family.permutations oracle).overlay.length initial).2.trans indexWord
      have preparedCount := (publicInversePrepared_public (state.family.permutations oracle).overlay.length initial oracle.castSucc 0 0 (by decide)).trans
        (stored.permutations oracle).base.count
      have preparedHistory := publicInversePrepared_sharedHistory (state.family.permutations oracle).overlay.length initial state.metadata past
        (fun current => by have := historyRoom current; omega)
      have retained := storedInverseSamples_sharedHistory attempts _ _ raw.1 raw.2 member oracle.castSucc
        state.metadata preparedHistory preparedIndex preparedCount (by have := room oracle; omega)
        (fun current => by have := historyRoom current; omega)
      have kept := storedInverseSamples_private attempts _ _ raw.1 raw.2 member oracle.castSucc 49 (by decide) (by decide)
        preparedIndex preparedCount (by have := room oracle; omega)
      have prepared : (publicInversePrepared (state.family.permutations oracle).overlay.length initial).ram 49#256 = initial.ram 49#256 := by
        rw [(publicInversePrepared_data _ initial).1]
        exact oracleLoadRam_private initial 49 (by decide) (by decide)
      have ram := recordedPublicInverseTail_nonfixedRam raw.1
        (by rw [kept, prepared, tag]; decide) (by rw [kept, prepared, tag]; decide)
      rw [memoryEq, ram]
      exact SharedHistoryMemory.fixedFrame raw.1.ram raw.1.ram state.metadata
        (state.metadata.record (.encInverse index value) reply) retained rfl
        (fun current => by have := historyRoom current; omega) (by intros; rfl)
  | hash key =>
      let initial := recordedPublicInputMemory memory (.hash key) rest
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_hashMemory attempts
        state.family.hash.length 0 memory (.hash key) rest rfl result supported
      have count : initial.ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.family.hash.length := by
        simpa only [hashWordPairs, List.length_map] using stored.hash.count
      have retained := hashHandlerSamples_sharedHistory _ initial raw.1 raw.2 member state.metadata past values.2.1 count
        (by omega) (fun current => by have := historyRoom current; omega)
      rw [memoryEq, recordedPublicHashTail_ram]
      exact SharedHistoryMemory.fixedFrame raw.1.ram raw.1.ram state.metadata
        (state.metadata.record (.hash key) reply) retained rfl
        (fun current => by have := historyRoom current; omega) (by intros; rfl)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
