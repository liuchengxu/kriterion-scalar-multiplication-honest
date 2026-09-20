import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultPhysical
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotFamilyReady
import Proof.Privacy.Simulator.Arithmetic.OracleHistoryFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The history relation stores its count and its ordered visible pairs. -/
structure HistoryMemory (ram : Word → Word) (oracle : Fin 15749) (pairs : List (Word × Word)) : Prop where
  count : ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 pairs.length
  stored : RepresentsPairs ram (oracleAddress oracle 3 256) pairs

/-- Agreement on the history region preserves the complete history relation. -/
theorem HistoryMemory.congr (original updated : Word → Word) (oracle : Fin 15749)
    (pairs : List (Word × Word)) (represented : HistoryMemory original oracle pairs)
    (fits : 256 + 2 * pairs.length < 2 ^ 110)
    (same : ∀ offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle 3 offset) = original (oracleAddress oracle 3 offset)) :
    HistoryMemory updated oracle pairs := by
  refine ⟨(same 0 (by decide)).trans represented.count, ?_⟩
  apply RepresentsPairs.congr pairs original updated _ represented.stored
  intro index bound
  rw [oracleAddress_add]
  exact same _ (by omega)

/-- The initial history has no pairs and a zero count. -/
theorem HistoryMemory.empty (ram : Word → Word) (oracle : Fin 15749)
    (zero : ram (oracleAddress oracle 3 0) = 0) : HistoryMemory ram oracle [] := by
  refine ⟨by simpa using zero, ?_⟩
  trivial

/-- The automatic command prefix preserves its visible history. -/
theorem checkedSlotPreparedRestored_history (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Word × Word)) (count : Nat)
    (represented : HistoryMemory memory.ram oracle pairs) (fits : 256 + 2 * pairs.length < 2 ^ 110) :
    HistoryMemory (checkedSlotRestored (checkedSlotPrepared count memory)).ram oracle pairs := by
  apply HistoryMemory.congr memory.ram _ oracle pairs represented fits
  intro offset bound
  rw [(checkedSlotPreparedRestored_data memory count).2.2]
  exact checkedSlotStart_public memory oracle 3 offset bound

/-- Every private query preserves its selected visible history. -/
theorem internalForwardSamples_historyMemory (attempts count overlayCount : Nat)
    (memory final : Memory) (cost : Nat) (oracle : Fin 15749) (pairs : List (Word × Word))
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support)
    (represented : HistoryMemory memory.ram oracle pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (historyFits : 256 + 2 * pairs.length < 2 ^ 110) :
    HistoryMemory final.ram oracle pairs :=
  HistoryMemory.congr memory.ram final.ram oracle pairs represented historyFits
    (internalForwardSamples_historyFrame attempts count overlayCount memory final cost supported
      oracle index counter fits)

/-- An accepted public fixed query appends exactly its visible pair. -/
theorem publicHistoryResult_historyMemory (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Word × Word)) (represented : HistoryMemory memory.ram oracle pairs)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (capacity : 257 + 2 * pairs.length < 2 ^ 110) (accepted : memory.registers 7 ≠ 0#256)
    (fixed : memory.ram 49#256 = 0#256 ∨ memory.ram 49#256 = 1#256) :
    HistoryMemory (publicHistoryResult memory).1.ram oracle
      (pairs ++ [(if memory.ram 49#256 = 0#256 then memory.ram 48 else memory.registers 8,
        if memory.ram 49#256 = 0#256 then memory.registers 8 else memory.ram 48)]) := by
  constructor
  · simpa only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] using
      publicHistoryResult_historyCount memory oracle pairs.length header represented.count accepted fixed
  · exact publicHistoryResult_historyPairs memory oracle pairs header represented.count represented.stored
      capacity accepted fixed

/-- A physical history append preserves the complete ordered history relation. -/
theorem historyAppended_memory (memory : Memory) (oracle : Fin 15749) (pairs : List (Word × Word))
    (represented : HistoryMemory memory.ram oracle pairs)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (capacity : 256 + 2 * (pairs.length + 1) < 2 ^ 110) :
    HistoryMemory (historyAppended memory).ram oracle
      (pairs ++ [(memory.registers 8, memory.registers 10)]) := by
  have selected := historyHeader_address memory oracle header
  constructor
  · rw [← selected, historyAppended_count, selected, represented.count]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, BitVec.ofNat_add]
  · have sourceBase : historyHeader memory + 256#256 = oracleAddress oracle 3 256 := by
      rw [selected]
      exact oracleAddress_add oracle 3 0 256
    have bounded : 2 * pairs.length + 2 ≤ 2 ^ 256 := by
      have : 2 ^ 110 < 2 ^ 256 := by decide
      omega
    have stored := historyAppended_represents memory pairs (by rw [selected]; exact represented.count)
      (by rw [sourceBase]; exact represented.stored) bounded (by
        intro index bound
        rw [sourceBase, selected, oracleAddress_add]
        intro same
        have offsets := (oracleAddress_injective oracle oracle 3 3 (256 + index) 0 (by omega) (by decide) same).2.2
        omega)
    simpa only [sourceBase] using stored

end Kriterion.ArgoMAC.ArithmeticSimulator
