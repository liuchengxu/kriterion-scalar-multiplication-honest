import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteMemory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHistory
import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine

/-- An internal read preserves all fixed histories. -/
theorem internalForwardSamples_sharedHistory (attempts count overlay : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlay memory).support)
    (oracle : Fin 15749) (metadata : Metadata) (represented : SharedHistoryMemory memory.ram metadata)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110) :
    SharedHistoryMemory final.ram metadata := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [(internalForwardTail_data overlay before).1]
  exact storedForwardSamples_sharedHistory attempts count memory before spent member oracle metadata
    represented index counter room historyRoom

/-- Each link row preserves every fixed history and the hash table. -/
theorem encLinkRowSamples_sharedHistory [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (metadata : Metadata) (history : SharedHistoryMemory memory.ram metadata)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkRowSamples attempts state memory index
      (indices.flatMap encLinkIndexBits ++ suffix) (encLinkInput memory firstKey)).support) :
    SharedHistoryMemory result.1.1.ram metadata ∧ result.2.hash = state.hash := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  let rest := indices.flatMap encLinkIndexBits ++ suffix
  have prepared := encLinkPrepared_family memory index rest state ready.represented ready.capacity
  have fit := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have room : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have preparedHistory : SharedHistoryMemory (encLinkPrepared memory index rest).ram metadata :=
    SharedHistoryMemory.fixedFrame _ _ metadata metadata history rfl historyRoom
      (fun current offset bound => encLinkPrepared_public memory index rest _ 3 offset bound)
  have rawHistory := internalForwardSamples_sharedHistory attempts _ _ _ before spent member
    (encLinkPhysicalIndex index).castSucc metadata preparedHistory
    (encLinkPrepared_values memory index rest).2.1
    (prepared.permutations (encLinkPhysicalIndex index)).base.count room historyRoom
  have cursor := encLinkRowQuery_private attempts state memory before spent index rest
    ready.represented ready.capacity room member 33 (by decide) (by decide) (by decide)
  change before.ram 33 = memory.ram 33 at cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have outputNat : (before.ram 33).toNat < 2 ^ 96 := by
    rw [cursor, ready.cursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans upper (by decide))]
    exact upper
  have apart (cell : Nat) (small : cell < 256) : before.ram 33 ≠ BitVec.ofNat 256 cell := by
    rw [cursor, ready.cursor]
    exact encLinkOutput_separate output cell ready.outputLower upper small
  refine ⟨?_, rfl⟩
  change SharedHistoryMemory (encLinkAfterQuery before).1.ram metadata
  exact SharedHistoryMemory.fixedFrame _ _ metadata metadata rawHistory rfl historyRoom
    (fun current offset bound => encLinkAfterQuery_public before outputNat
      (apart 32 (by decide)) (apart 38 (by decide)) _ 3 offset bound)

/-- An accepted link loop retains the histories and bounds all source counts. -/
theorem encLinkLoopSamples_sharedMemory [BN254.FieldCertificate]
    (attempts : Nat) (firstKey : Block) (suffix : List Bool) (indices : List EncPRF.PermutationIndex)
    (memory : Memory) (state : SparseOracleFamily) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory indices suffix firstKey output limit)
    (metadata : Metadata) (history : SharedHistoryMemory memory.ram metadata)
    (historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs metadata.fixedTranscript current).length < 2 ^ 110)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support)
    (accepted : result.1.2.2 ≠ 7467) :
    SharedHistoryMemory result.1.1.ram metadata ∧ result.2.hash = state.hash ∧
    (∀ index, (result.2.permutations index).base.used ≤ limit + indices.length) ∧
    (∀ index, (result.2.permutations index).overlay.length ≤ limit + indices.length) := by
  induction indices generalizing memory state output limit result with
  | nil =>
      have equal : result = ((memory, 0, 7466), state) := by simpa [encLinkLoopSamples] using supported
      subst result
      exact ⟨history, rfl, ready.baseCount, ready.overlayCount⟩
  | cons index indices ih =>
      obtain ⟨row, rowMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have progress := encLinkRowSamples_progress attempts state memory index indices suffix firstKey output limit ready row rowMember
      have kept := encLinkRowSamples_sharedHistory attempts state memory index indices suffix firstKey output limit
        ready metadata history historyRoom row rowMember
      change result ∈ (if row.1.2.2 = 7467 then PMF.pure row else
        (encLinkLoopSamples attempts firstKey suffix indices row.1.1 row.2).map (encLinkCharge row.1.2.1)).support at member
      by_cases failed : row.1.2.2 = 7467
      · rw [if_pos failed] at member
        have equal : result = row := by simpa using member
        exact False.elim (accepted (equal ▸ failed))
      · rw [if_neg failed] at member
        obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
        have next := ih row.1.1 row.2 (output + 1) (limit + 1) (progress.resolve_left failed).1
          kept.1 tail tailMember accepted
        refine ⟨next.1, next.2.1.trans kept.2, ?_, ?_⟩
        · intro current
          have bound := next.2.2.1 current
          simpa only [encLinkCharge, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using bound
        · intro current
          have bound := next.2.2.2 current
          simpa only [encLinkCharge, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using bound

/-- The complete link retains the shared source and adds at most 508 base entries. -/
theorem encLinkSamples_sharedMemory [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SharedOracleSource) (key : BN254.BaseField)
    (output limit : Nat) (suffix : List Bool)
    (represented : SharedSourceMemory memory state limit)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = suffix)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkSamples attempts memory state.family key suffix).support)
    (accepted : result.1.2.2 ≠ 7467) :
    SharedSourceMemory result.1.1 (SharedOracleSource.mk result.2 state.metadata) (limit + 508) ∧
      result.2.hash.length ≤ state.family.hash.length + 1 := by
  obtain ⟨hash, hashMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have ready := encLinkInitialize_ready memory hash.1 hash.2 state.family key output limit suffix
    represented.family represented.capacity operand outputBase outputLower outputUpper
    represented.counts.1 represented.counts.2.1 room hashRoom wire hashMember
  have historyRoom : ∀ current, 256 + 2 * (recordHistoryPairs state.metadata.fixedTranscript current).length < 2 ^ 110 := by
    intro current
    have bounded := represented.counts.2.2 current
    omega
  have savedHistory := SharedHistoryMemory.fixedFrame _ _ state.metadata state.metadata
    represented.history rfl historyRoom
    (fun current offset bound => encLinkSaved_public memory _ 3 offset bound)
  have saved := encLinkSaved_family memory state.family represented.family represented.capacity
  have counter : (encLinkSaved memory).ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.family.hash.length := by
    simpa only [hashWordPairs, List.length_map] using saved.hash.count
  have hashHistory := hashHandlerSamples_sharedHistory state.family.hash.length _ hash.1 hash.2 hashMember
    state.metadata savedHistory (encLinkSave_state memory).2.1 counter (by omega) historyRoom
  have scheduledHistory := SharedHistoryMemory.fixedFrame _ _ state.metadata state.metadata
    hashHistory rfl historyRoom
    (fun current offset bound => encLinkScheduled_public hash.1 _ 3 offset bound)
  have next := encLinkLoopSamples_sharedMemory attempts _ suffix encLinkIndices _ _ output limit ready
    state.metadata scheduledHistory historyRoom tail tailMember accepted
  have family := encLinkLoopSamples_memory attempts _ suffix encLinkIndices _ _ output limit ready tail tailMember
  have length : encLinkIndices.length = 508 := by simp [encLinkIndices, coordinateBitCount]
  refine ⟨⟨family.1, family.2.1, next.1, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [encLinkCharge, length] using next.2.2.1
  · simpa only [encLinkCharge, length] using next.2.2.2
  · intro current
    exact (represented.counts.2.2 current).trans (Nat.le_add_right _ _)
  · change tail.2.hash.length ≤ state.family.hash.length + 1
    rw [next.2.1]
    change (hashNextTable state.family.hash key (hash.1.registers 8).toFin).length ≤ _
    unfold hashNextTable
    split <;> simp

end Kriterion.ArgoMAC.ArithmeticSimulator
