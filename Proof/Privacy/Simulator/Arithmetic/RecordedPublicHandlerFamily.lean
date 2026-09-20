import Proof.Privacy.Simulator.Arithmetic.RecordedPublicSampleMemory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicOtherFamily

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- Every typed successful handler reply retains its exact complete finite oracle family. -/
theorem recordedPublicHandlerSamples_family [BN254.FieldCertificate]
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
    OracleFamilyMemory result.1.memory.ram (sharedPublicNextFamily state.family request reply) ∧
      OracleFamilyFits (sharedPublicNextFamily state.family request reply) := by
  have blockSame : Security.SimulatorMachine.blockFin = blockFin := rfl
  have hashSame : Security.SimulatorMachine.hashFin = hashFin := rfl
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
      have accepted := publicForwardReplyValue_some (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value) _ raw.1 reply observed
      have recovered := programmedForwardMemoryState_reply (state.family.permutations oracle) (blockFin value)
        raw.1 reply accepted.1 accepted.2
      have family := storedForwardSamples_recordedFamily attempts initial raw.1 raw.2 state.family oracle (blockFin value)
        (recordHistoryPairs state.metadata.fixedTranscript index).length stored capacity indexWord operand (room oracle)
        (past index).count (historyRoom index) member
      rw [memoryEq]
      rw [blockSame] at recovered
      simpa only [sharedPublicNextFamily, recovered, oracle, publicSourceOverlay, publicSourceOracle] using family
  | encForward index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      let initial := recordedPublicInputMemory memory (.encForward index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_forwardMemory attempts
        (publicSourceCount state (.encForward index value)) (publicSourceOverlay state (.encForward index value)) memory (.encForward index value) rest rfl result supported
      have typed := recordedPublicForwardTail_answer (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value)
        (by intro key; simp) (state.family.permutations oracle).overlay.length raw.1
        ((congrFun (storedForwardSamples_bits attempts _ initial raw.1 raw.2 member) 3).trans outputEmpty)
        (stable raw member)
      have observed : publicForwardReplyValue (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value)
          (state.family.permutations oracle).overlay.length raw.1 = some reply := typed.symm.trans (memoryEq ▸ answered)
      have accepted := publicForwardReplyValue_some (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value) _ raw.1 reply observed
      have recovered := programmedForwardMemoryState_reply (state.family.permutations oracle) (blockFin value)
        raw.1 reply accepted.1 accepted.2
      have tag : initial.ram 49#256 = 2#256 := saved.2
      have family := storedForwardSamples_otherFamily attempts initial raw.1 raw.2 state.family oracle (blockFin value)
        stored capacity indexWord operand (room oracle) (by rw [tag]; decide) (by rw [tag]; decide) member
      rw [memoryEq]
      rw [blockSame] at recovered
      simpa only [sharedPublicNextFamily, recovered, oracle, publicSourceOverlay, publicSourceOracle] using family
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
      have accepted := publicReplyValue_some (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value) raw.1 reply observed
      have recovered := programmedInverseMemoryState_reply (state.family.permutations oracle) (blockFin value)
        raw.1 reply accepted.1 accepted.2
      have family := storedInverseSamples_recordedFamily attempts initial raw.1 raw.2 state.family oracle (blockFin value)
        (recordHistoryPairs state.metadata.fixedTranscript index).length stored capacity indexWord operand (room oracle)
        (past index).count (historyRoom index) member
      rw [memoryEq]
      rw [blockSame] at recovered
      simpa only [sharedPublicNextFamily, recovered, oracle, publicSourceOverlay, publicSourceOracle] using family
  | encInverse index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      let initial := recordedPublicInputMemory memory (.encInverse index value) rest
      have indexWord : initial.registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : initial.registers 8 = BitVec.ofNat 256 (blockFin value).val := values.1
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_inverseMemory attempts
        (publicSourceCount state (.encInverse index value)) (publicSourceOverlay state (.encInverse index value)) memory (.encInverse index value) rest rfl result supported
      have typed := recordedPublicInverseTail_answer (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value)
        (by intro key; simp) raw.1
        ((congrFun (storedInverseSamples_bits attempts _ _ raw.1 raw.2 member) 3).trans
          ((congrFun (publicInversePrepared_bits _ initial) 3).trans outputEmpty)) (stable raw member)
      have observed : publicReplyValue (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value)
          raw.1 = some reply := typed.symm.trans (memoryEq ▸ answered)
      have accepted := publicReplyValue_some (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value) raw.1 reply observed
      have recovered := programmedInverseMemoryState_reply (state.family.permutations oracle) (blockFin value)
        raw.1 reply accepted.1 accepted.2
      have tag : initial.ram 49#256 = 3#256 := saved.2
      have family := storedInverseSamples_otherFamily attempts initial raw.1 raw.2 state.family oracle (blockFin value)
        stored capacity indexWord operand (room oracle) (by rw [tag]; decide) (by rw [tag]; decide) member
      rw [memoryEq]
      rw [blockSame] at recovered
      simpa only [sharedPublicNextFamily, recovered, oracle, publicSourceOverlay, publicSourceOracle] using family
  | hash key =>
      let initial := recordedPublicInputMemory memory (.hash key) rest
      obtain ⟨raw, member, memoryEq⟩ := recordedPublicHandlerSamples_hashMemory attempts
        state.family.hash.length 0 memory (.hash key) rest rfl result supported
      have typed := publicHashTail_answer (FixedIndex := Shared.FixedKeyIndex) (EncIndex := EncPRF.PermutationIndex) key raw.1
        ((congrFun (hashHandlerSamples_bits state.family.hash.length initial raw.1 raw.2 member) 3).trans outputEmpty)
      have observed : publicReplyValue (PublicQuery.hash (FixedIndex := Shared.FixedKeyIndex) (EncIndex := EncPRF.PermutationIndex) key)
          raw.1 = some reply := typed.symm.trans (memoryEq ▸ answered)
      have accepted := publicReplyValue_some (PublicQuery.hash (FixedIndex := Shared.FixedKeyIndex) (EncIndex := EncPRF.PermutationIndex) key) raw.1 reply observed
      have finite : (raw.1.registers 8).toFin = hashFin reply := by
        simpa only [publicAnswerValue, hashSame, Equiv.apply_symm_apply] using congrArg hashFin accepted.2
      have family := hashHandlerSamples_family initial raw.1 raw.2 state.family key stored capacity values.2.1 values.1 hashRoom member
      have fits : OracleFamilyFits (state.family.updateHash (hashNextTable state.family.hash key (raw.1.registers 8).toFin)) := by
        refine ⟨capacity.base, capacity.overlay, ?_⟩
        change 2 * (hashNextTable state.family.hash key (raw.1.registers 8).toFin).length ≤ 2 ^ 110
        unfold hashNextTable
        split <;> (try simp only [List.length_cons]) <;> omega
      rw [publicHashTail_ram] at family
      rw [memoryEq, recordedPublicHashTail_ram]
      simpa only [sharedPublicNextFamily, finite] using And.intro family fits

end
end Kriterion.ArgoMAC.ArithmeticSimulator
