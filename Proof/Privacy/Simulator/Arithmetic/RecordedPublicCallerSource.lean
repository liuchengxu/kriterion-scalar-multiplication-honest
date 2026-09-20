import Proof.Privacy.Simulator.Arithmetic.RecordedPublicCaller
import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- Every actual public query preserves the private buffers of the simulator. -/
theorem recordedPublicHandlerSamples_private [BN254.FieldCertificate]
    (attempts limit : Nat) (memory : Memory) (source : SharedOracleSource) (request : SharedQuery)
    (rest : List Bool) (represented : SharedSourceMemory memory source limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (hashBound : source.family.hash.length ≤ limit)
    (result : Configuration 1810 × Nat)
    (supported : some result ∈ (recordedPublicHandlerSamples attempts (publicSourceCount source request)
      (publicSourceOverlay source request) memory request rest).support)
    (cell : Nat) (lower : 51 ≤ cell) (upper : cell < 2 ^ 96) :
    result.1.memory.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have family := recordedPublicInputMemory_family memory request rest source.family represented.family represented.capacity
  have values := recordedPublicInputMemory_values memory request rest
  have saved := recordedPublicInputMemory_saved memory request rest
  have history := recordedPublicInputMemory_sharedHistory memory source.metadata request rest represented.history
    (fun index => by have := represented.counts.2.2 index; omega)
  have keep := recordedPublicInputMemory_private memory request rest cell lower upper
  have baseRoom : ∀ index, 2 * ((source.family.permutations index).base.used + 1) ≤ 2 ^ 110 := by
    intro index
    have := represented.counts.1 index
    omega
  have historyRoom : ∀ index, 257 + 2 * (recordHistoryPairs source.metadata.fixedTranscript index).length < 2 ^ 110 := by
    intro index
    have := represented.counts.2.2 index
    omega
  cases request with
  | fixedForward index value =>
    let oracle := sharedPhysicalIndex (.inl index)
    let input := recordedPublicInputMemory memory (.fixedForward index value) rest
    have selected : input.registers 9 = BitVec.ofNat 256 oracle.val := by
      rw [values.2.1]
      simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
    obtain ⟨raw, member, same⟩ := recordedPublicHandlerSamples_forwardMemory attempts _ _ memory
      (.fixedForward index value) rest rfl result supported
    rw [same]
    exact (storedForwardSamples_recordedPrivate attempts _ _ input raw.1 raw.2 member oracle.castSucc
      _ cell lower upper selected (family.permutations oracle).base.count (history index).count
      (baseRoom oracle) (historyRoom index)).trans keep
  | fixedInverse index value =>
    let oracle := sharedPhysicalIndex (.inl index)
    let input := recordedPublicInputMemory memory (.fixedInverse index value) rest
    let overlayCount := (source.family.permutations oracle).overlay.length
    let prepared := publicInversePrepared overlayCount input
    have selected : input.registers 9 = BitVec.ofNat 256 oracle.val := by
      rw [values.2.1]
      simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
    obtain ⟨raw, member, same⟩ := recordedPublicHandlerSamples_inverseMemory attempts _ _ memory
      (.fixedInverse index value) rest rfl result supported
    have indexWord := (publicInversePrepared_data overlayCount input).2.trans selected
    have counter := (publicInversePrepared_public overlayCount input oracle.castSucc 0 0 (by decide)).trans
      (family.permutations oracle).base.count
    have past := (publicInversePrepared_public overlayCount input oracle.castSucc 3 0 (by decide)).trans
      (history index).count
    rw [same]
    exact (storedInverseSamples_recordedPrivate attempts _ prepared raw.1 raw.2 member oracle.castSucc
      _ cell lower upper indexWord counter past (baseRoom oracle) (historyRoom index)).trans
      ((publicInversePrepared_private overlayCount input cell lower upper).trans keep)
  | encForward index value =>
    let oracle := sharedPhysicalIndex (.inr index)
    let input := recordedPublicInputMemory memory (.encForward index value) rest
    have selected : input.registers 9 = BitVec.ofNat 256 oracle.val := by
      rw [values.2.1]
      simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
    obtain ⟨raw, member, same⟩ := recordedPublicHandlerSamples_forwardMemory attempts _ _ memory
      (.encForward index value) rest rfl result supported
    have tag := (storedForwardSamples_private attempts _ input raw.1 raw.2 member oracle.castSucc 49
      (by decide) (by decide) selected (family.permutations oracle).base.count (baseRoom oracle)).trans saved.2
    change raw.1.ram 49#256 = 2#256 at tag
    rw [same, recordedPublicForwardTail_nonfixedRam _ _ (by rw [tag]; decide) (by rw [tag]; decide)]
    exact (storedForwardSamples_private attempts _ input raw.1 raw.2 member oracle.castSucc cell
      (by omega) upper selected (family.permutations oracle).base.count (baseRoom oracle)).trans keep
  | encInverse index value =>
    let oracle := sharedPhysicalIndex (.inr index)
    let input := recordedPublicInputMemory memory (.encInverse index value) rest
    let overlayCount := (source.family.permutations oracle).overlay.length
    let prepared := publicInversePrepared overlayCount input
    have selected : input.registers 9 = BitVec.ofNat 256 oracle.val := by
      rw [values.2.1]
      simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
    obtain ⟨raw, member, same⟩ := recordedPublicHandlerSamples_inverseMemory attempts _ _ memory
      (.encInverse index value) rest rfl result supported
    have indexWord := (publicInversePrepared_data overlayCount input).2.trans selected
    have counter := (publicInversePrepared_public overlayCount input oracle.castSucc 0 0 (by decide)).trans
      (family.permutations oracle).base.count
    have preparedTag : prepared.ram 49#256 = input.ram 49#256 := by
      rw [(publicInversePrepared_data overlayCount input).1]
      exact oracleLoadRam_private input 49 (by decide) (by decide)
    have tag := (storedInverseSamples_private attempts _ prepared raw.1 raw.2 member oracle.castSucc 49
      (by decide) (by decide) indexWord counter (baseRoom oracle)).trans (preparedTag.trans saved.2)
    change raw.1.ram 49#256 = 3#256 at tag
    rw [same, recordedPublicInverseTail_nonfixedRam _ (by rw [tag]; decide) (by rw [tag]; decide)]
    exact (storedInverseSamples_private attempts _ prepared raw.1 raw.2 member oracle.castSucc cell
      (by omega) upper indexWord counter (baseRoom oracle)).trans
      ((publicInversePrepared_private overlayCount input cell lower upper).trans keep)
  | hash value =>
    let input := recordedPublicInputMemory memory (.hash value) rest
    have selected : input.registers 9 = BitVec.ofNat 256 15748 := values.2.1
    obtain ⟨raw, member, same⟩ := recordedPublicHandlerSamples_hashMemory attempts _ _ memory
      (.hash value) rest rfl result supported
    rw [same, recordedPublicHashTail_ram]
    exact (hashHandlerSamples_private _ input raw.1 raw.2 member 15748 selected
      (by simpa only [publicSourceCount, hashWordPairs, List.length_map] using family.hash.count)
      (by simp only [publicSourceCount]; omega) cell (by omega) upper).trans keep

end
end Kriterion.ArgoMAC.ArithmeticSimulator
