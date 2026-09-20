import Proof.Privacy.Simulator.Arithmetic.RecordedPublicTyped
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryResultPhysical
import Proof.Privacy.Simulator.Arithmetic.OracleHistoryFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The stored inverse query restores its physical oracle header on every path. -/
theorem storedInverseSamples_header (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) : final.registers 6 = oracleAddress oracle 0 0 := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have metadata := inverseLoaded_metadata memory
  have inputBase := metadata.2.2.1.trans (oracleLoaded_outputBase memory oracle count index counter (by omega))
  have outputBase := metadata.2.2.2.1.trans (oracleLoaded_inputBase memory oracle count index counter (by omega))
  have saved := permutationForwardSamples_savedHeader attempts count (inverseLoaded memory) before spent member
    oracle 1 0 inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 :=
    saved.trans ((congrFun metadata.1 13).trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address])))
  simpa [inverseCommitted, oracleCommitted, metadataSwapped] using header

/-- Every forward history tail preserves the answer under the physical capacity bound. -/
theorem recordedPublicForward_stable (attempts count overlayCount historyCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (historyFits : 257 + 2 * historyCount < 2 ^ 110) :
    RecordedPublicReplyStable .forward attempts count overlayCount memory := by
  intro result supported
  have frame := storedForwardSamples_historyFrame attempts count memory result.1 result.2 supported oracle index counter fits
  have scan := overlayForward_data overlayCount result.1
  apply publicHistoryResult_physicalReply _ oracle historyCount
  · exact (scan.2.2 6 (by decide)).trans frame.1
  · exact (congrFun scan.1 _).trans ((frame.2 0 (by decide)).trans history)
  · exact historyFits

/-- Every inverse history tail preserves the answer under the physical capacity bound. -/
theorem recordedPublicInverse_stable (attempts count overlayCount historyCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (historyFits : 257 + 2 * historyCount < 2 ^ 110) :
    RecordedPublicReplyStable .inverse attempts count overlayCount memory := by
  intro result supported
  have preparedIndex := (publicInversePrepared_data overlayCount memory).2.trans index
  have preparedCounter := (publicInversePrepared_public overlayCount memory oracle 0 0 (by decide)).trans counter
  have header := storedInverseSamples_header attempts count (publicInversePrepared overlayCount memory)
    result.1 result.2 supported oracle preparedIndex preparedCounter fits
  have historyFrame := storedInverseSamples_historyFrame attempts count (publicInversePrepared overlayCount memory)
    result.1 result.2 supported oracle preparedIndex preparedCounter fits 0 (by decide)
  apply publicHistoryResult_physicalReply result.1 oracle historyCount header
  · exact historyFrame.trans ((publicInversePrepared_public overlayCount memory oracle 3 0 (by decide)).trans history)
  · exact historyFits

/-- Every canonical branch preserves its history reply under the physical count bounds. -/
theorem recordedPublic_stable (kind : PublicHandlerKind) (attempts count overlayCount historyCount : Nat)
    (memory : Memory) (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (history : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 historyCount)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (historyFits : 257 + 2 * historyCount < 2 ^ 110) :
    RecordedPublicReplyStable kind attempts count overlayCount memory := by
  cases kind with
  | forward => exact recordedPublicForward_stable attempts count overlayCount historyCount memory oracle index counter history fits historyFits
  | inverse => exact recordedPublicInverse_stable attempts count overlayCount historyCount memory oracle index counter history fits historyFits
  | hash => trivial

end Kriterion.ArgoMAC.ArithmeticSimulator
