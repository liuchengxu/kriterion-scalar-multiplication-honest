import Proof.Privacy.Simulator.Arithmetic.PublicHistoryBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source records only accepted external fixed-key queries. -/
def publicHistoryResult (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 1)
  else if memory.ram 49#256 = 0#256 then
    (publicHistoryFinished (executeLinear publicHistoryForward (publicHistoryForwardReady memory)), 27)
  else if memory.ram 49#256 = 1#256 then
    (publicHistoryFinished (executeLinear publicHistoryInverse (publicHistoryInverseReady memory)), 28)
  else (publicHistoryInverseReady memory, 7)

/-- The host records the visible pair and retains all unused caller fuel. -/
theorem publicHistoryBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 35 → Fin (host.size + 1)) (present : ContainsPublicHistory host labels)
    (memory : Memory) (fuel : Nat) :
    run host (28 + fuel) ⟨labels 0, memory⟩ =
      (run host (28 + fuel - (publicHistoryResult memory).2)
        ⟨labels 34, (publicHistoryResult memory).1⟩).map
          (Option.map fun result => (result.1, result.2 + (publicHistoryResult memory).2)) := by
  have sub1 : 28 + fuel - 1 = 27 + fuel := by omega
  have sub27 : 28 + fuel - 27 = 1 + fuel := by omega
  have sub28 : 28 + fuel - 28 = fuel := by omega
  have sub7 : 28 + fuel - 7 = 21 + fuel := by omega
  by_cases rejected : memory.registers 7 = 0#256
  · simpa [publicHistoryResult, rejected, ← Nat.add_assoc, sub1] using
      publicHistoryBlock_rejected host labels present memory (27 + fuel) rejected
  · by_cases forward : memory.ram 49#256 = 0#256
    · simpa [publicHistoryResult, rejected, forward, ← Nat.add_assoc, sub27] using
        publicHistoryBlock_forward host labels present memory (1 + fuel) rejected forward
    · by_cases inverse : memory.ram 49#256 = 1#256
      · simpa [publicHistoryResult, rejected, forward, inverse, sub28] using
          publicHistoryBlock_inverse host labels present memory fuel rejected inverse
      · simpa [publicHistoryResult, rejected, forward, inverse, ← Nat.add_assoc, sub7] using
          publicHistoryBlock_other host labels present memory (21 + fuel) rejected forward inverse

/-- The history tail never changes any bit stack. -/
theorem publicHistoryResult_bits (memory : Memory) :
    (publicHistoryResult memory).1.bits = memory.bits := by
  unfold publicHistoryResult
  split
  · rfl
  · split
    · change (executeLinear publicHistoryRestore (historyAppended _)).bits = _
      rw [(publicHistoryRestore_state _).2.2, (historyAppended_data _).2.2.2.2]
      exact (publicHistoryForward_state _).2.2.2.2.2
    · split
      · change (executeLinear publicHistoryRestore (historyAppended _)).bits = _
        rw [(publicHistoryRestore_state _).2.2, (historyAppended_data _).2.2.2.2]
        exact (publicHistoryInverse_state _).2.2.2.2.2
      · rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
