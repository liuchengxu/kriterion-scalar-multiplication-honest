import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A forward encryption query preserves its reply without a fixed-history bound. -/
theorem recordedPublicForward_nonfixedStable (attempts count overlayCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256) :
    RecordedPublicReplyStable .forward attempts count overlayCount memory := by
  intro result member
  have saved := storedForwardSamples_private attempts count memory result.1 result.2 member
    oracle 49 (by decide) (by decide) index counter room
  change result.1.ram 49#256 = memory.ram 49#256 at saved
  have kept := (congrFun (overlayForward_data overlayCount result.1).1 (49#256 : Word)).trans saved
  exact (publicHistoryResult_nonfixed _ (by rw [kept]; exact forward) (by rw [kept]; exact inverse)).2

/-- An inverse encryption query preserves its reply without a fixed-history bound. -/
theorem recordedPublicInverse_nonfixedStable (attempts count overlayCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (room : 2 * (count + 1) ≤ 2 ^ 110)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256) :
    RecordedPublicReplyStable .inverse attempts count overlayCount memory := by
  intro result member
  have preparedIndex := (publicInversePrepared_data overlayCount memory).2.trans index
  have preparedCount := (publicInversePrepared_public overlayCount memory oracle 0 0 (by decide)).trans counter
  have saved := storedInverseSamples_private attempts count (publicInversePrepared overlayCount memory)
    result.1 result.2 member oracle 49 (by decide) (by decide) preparedIndex preparedCount room
  have prepared : (publicInversePrepared overlayCount memory).ram 49#256 = memory.ram 49#256 := by
    rw [(publicInversePrepared_data overlayCount memory).1]
    exact oracleLoadRam_private memory 49 (by decide) (by decide)
  change result.1.ram 49#256 = (publicInversePrepared overlayCount memory).ram 49#256 at saved
  have kept := saved.trans prepared
  exact (publicHistoryResult_nonfixed _ (by rw [kept]; exact forward) (by rw [kept]; exact inverse)).2

/-- A forward encryption tail preserves the complete oracle RAM. -/
theorem recordedPublicForwardTail_nonfixedRam (count : Nat) (memory : Memory)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256) :
    (recordedPublicForwardTail count memory).1.ram = memory.ram := by
  unfold recordedPublicForwardTail
  split
  · rfl
  · rw [wordOutput_ram]
    have scan := (overlayForward_data count memory).1
    have kept := publicHistoryResult_nonfixed (overlayForwardScan count memory).1
      (by rw [scan]; exact forward) (by rw [scan]; exact inverse)
    exact kept.1.trans scan

/-- An inverse encryption tail preserves the complete oracle RAM. -/
theorem recordedPublicInverseTail_nonfixedRam (memory : Memory)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256) :
    (recordedPublicInverseTail memory).1.ram = memory.ram := by
  unfold recordedPublicInverseTail
  split
  · rfl
  · rw [wordOutput_ram]
    exact (publicHistoryResult_nonfixed memory forward inverse).1

/-- The hash output tail preserves the complete oracle RAM. -/
theorem recordedPublicHashTail_ram (memory : Memory) :
    (recordedPublicHashTail memory).1.ram = memory.ram := by
  unfold recordedPublicHashTail
  split
  · rfl
  · exact hashOutput_ram memory

end Kriterion.ArgoMAC.ArithmeticSimulator
