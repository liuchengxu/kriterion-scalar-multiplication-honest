import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerOutputCode
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The final public label returns without a further memory change. -/
theorem recordedPublicHandler_halt [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (fuel + 1) ⟨1770, memory⟩ =
      PMF.pure (some (⟨1770, memory⟩, 1)) := by
  apply handlerHalt
  exact recordedPublicHandler_haltCode attempts

/-- The permutation output writes its wire answer and returns after 385 instructions. -/
theorem recordedPublicHandler_blockReply [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (385 + extra) ⟨616, memory⟩ =
      PMF.pure (some (⟨1770, executeLinear (wordOutput 128) memory⟩, 385)) := by
  have output := linear_continue (recordedPublicHandler attempts) (wordOutput 128) (recordedPublicCore ∘ publicBlockOutputLabels)
    (recordedPublicHandler_blockOutput attempts) memory (extra + 1)
  rw [wordOutput_length] at output
  change run (recordedPublicHandler attempts) (384 + (extra + 1)) ⟨616, memory⟩ = _ at output
  rw [show 385 + extra = 384 + (extra + 1) by omega, output]
  change (run (recordedPublicHandler attempts) (extra + 1) ⟨1770, executeLinear (wordOutput 128) memory⟩).map _ = _
  rw [recordedPublicHandler_halt, PMF.pure_map]
  rfl

/-- The hash output writes both wire blocks and returns after 771 instructions. -/
theorem recordedPublicHandler_hashReply [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (771 + extra) ⟨1000, memory⟩ =
      PMF.pure (some (⟨1770, executeLinear hashOutput memory⟩, 771)) := by
  have output := linear_continue (recordedPublicHandler attempts) hashOutput (recordedPublicCore ∘ publicHashOutputLabels)
    (recordedPublicHandler_hashOutput attempts) memory (extra + 1)
  rw [hashOutput_length] at output
  change run (recordedPublicHandler attempts) (770 + (extra + 1)) ⟨1000, memory⟩ = _ at output
  rw [show 771 + extra = 770 + (extra + 1) by omega, output]
  change (run (recordedPublicHandler attempts) (extra + 1) ⟨1770, executeLinear hashOutput memory⟩).map _ = _
  rw [recordedPublicHandler_halt, PMF.pure_map]
  rfl

/-- The forward handler checks the cutoff flag before it applies the overlay. -/
theorem recordedPublicHandler_forwardGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (fuel + 1) ⟨280, memory⟩ =
      (run (recordedPublicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 281, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  exact recordedPublicHandler_forwardGateCode attempts

/-- The inverse handler checks the cutoff flag before it emits an answer. -/
theorem recordedPublicHandler_inverseGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (fuel + 1) ⟨541, memory⟩ =
      (run (recordedPublicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 1776, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  exact recordedPublicHandler_inverseGateCode attempts

/-- The hash handler checks its success flag before it emits both answer blocks. -/
theorem recordedPublicHandler_hashGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (fuel + 1) ⟨615, memory⟩ =
      (run (recordedPublicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 1000, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  exact recordedPublicHandler_hashGateCode attempts

/-- The cutoff return does not write an answer. -/
theorem recordedPublicHandler_abort [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (fuel + 1) ⟨1771, memory⟩ =
      PMF.pure (some (⟨1771, memory⟩, 1)) := by
  apply handlerHalt
  exact recordedPublicHandler_abortCode attempts

/-- The history block records the reply before the answer writer uses it. -/
theorem recordedPublicHandler_historyReply [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (413 + extra) ⟨1776, memory⟩ =
      PMF.pure (some (⟨1770, executeLinear (wordOutput 128) (publicHistoryResult memory).1⟩,
        385 + (publicHistoryResult memory).2)) := by
  have executed := publicHistoryBlock_continue (recordedPublicHandler attempts) recordedPublicHistoryLabels
    (recordedPublicHandler_history attempts) memory (385 + extra)
  change run (recordedPublicHandler attempts) (28 + (385 + extra)) ⟨1776, memory⟩ = _ at executed
  have bound : (publicHistoryResult memory).2 ≤ 28 := by
    unfold publicHistoryResult
    split
    · omega
    · split
      · omega
      · split <;> omega
  rw [show 413 + extra = 28 + (385 + extra) by omega, executed]
  change (run (recordedPublicHandler attempts) (28 + (385 + extra) - (publicHistoryResult memory).2)
    ⟨616, (publicHistoryResult memory).1⟩).map _ = _
  rw [show 28 + (385 + extra) - (publicHistoryResult memory).2 =
      385 + (28 + extra - (publicHistoryResult memory).2) by omega,
    recordedPublicHandler_blockReply, PMF.pure_map]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
