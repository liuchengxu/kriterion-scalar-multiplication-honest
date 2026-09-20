import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerOutput
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTail

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward tail either aborts or applies the overlay and emits one block. -/
def recordedPublicForwardTail (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else
    let scanned := overlayForwardScan count memory
    (executeLinear (wordOutput 128) (publicHistoryResult scanned.1).1,
      scanned.2 + (385 + (publicHistoryResult scanned.1).2) + 1)

/-- The inverse tail either aborts or emits its one-block answer. -/
def recordedPublicInverseTail (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else (executeLinear (wordOutput 128) (publicHistoryResult memory).1,
    385 + (publicHistoryResult memory).2 + 1)

/-- The hash tail either aborts or emits its two-block answer. -/
def recordedPublicHashTail (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else (executeLinear hashOutput memory, 772)

/-- The final label records whether the handler returned a wire answer. -/
def recordedPublicTailLabel (memory : Memory) : Fin 1810 :=
  if memory.registers 7 = 0#256 then 1771 else 1770

/-- The complete forward tail includes its flag check, overlay scan, output, and halt. -/
theorem recordedPublicHandler_forwardTail [BN254.FieldCertificate] (attempts count extra : Nat)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 count) :
    run (recordedPublicHandler attempts) (11 * count + 421 + extra) ⟨280, memory⟩ =
      PMF.pure (some (⟨recordedPublicTailLabel memory, (recordedPublicForwardTail count memory).1⟩,
        (recordedPublicForwardTail count memory).2)) := by
  rw [show 11 * count + 421 + extra = (11 * count + 420 + extra) + 1 by omega,
    recordedPublicHandler_forwardGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 11 * count + 420 + extra = (11 * count + 419 + extra) + 1 by omega,
      recordedPublicHandler_abort, PMF.pure_map]
    simp [recordedPublicTailLabel, recordedPublicForwardTail, rejected]
    rfl
  · rw [if_neg rejected]
    have bound := overlayForward_cost count memory
    let remaining := 11 * count + 420 + extra - (overlayForwardScan count memory).2
    have enough : 413 ≤ remaining := by dsimp [remaining]; omega
    have scanned := overlayForward_continue (recordedPublicHandler attempts) (recordedPublicRedirect ∘ publicOverlayLoadLabels) (recordedPublicRedirect ∘ publicOverlayScanLabels)
      (recordedPublicHandler_overlayLoad attempts) (recordedPublicHandler_overlayScan attempts) rfl count memory fits counter remaining
    change run (recordedPublicHandler attempts) _ ⟨281, memory⟩ = _ at scanned
    have reserve : 11 * count + 420 + extra = (overlayForwardScan count memory).2 + remaining := by
      dsimp [remaining]; omega
    rw [reserve, scanned]
    change ((run (recordedPublicHandler attempts) remaining
      ⟨1776, (overlayForwardScan count memory).1⟩).map _).map _ = _
    rw [show remaining = 413 + (remaining - 413) by omega, recordedPublicHandler_historyReply,
      PMF.pure_map, PMF.pure_map]
    simp [recordedPublicForwardTail, recordedPublicTailLabel, rejected, Nat.add_assoc, Nat.add_comm]
    rw [← Nat.add_assoc]
    rfl

/-- The complete inverse tail rejects a cutoff result before it writes any bits. -/
theorem recordedPublicHandler_inverseTail [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (414 + extra) ⟨541, memory⟩ =
      PMF.pure (some (⟨recordedPublicTailLabel memory, (recordedPublicInverseTail memory).1⟩,
        (recordedPublicInverseTail memory).2)) := by
  rw [show 414 + extra = (413 + extra) + 1 by omega, recordedPublicHandler_inverseGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 413 + extra = (412 + extra) + 1 by omega, recordedPublicHandler_abort, PMF.pure_map]
    simp [recordedPublicTailLabel, recordedPublicInverseTail, rejected]
    rfl
  · rw [if_neg rejected]
    rw [recordedPublicHandler_historyReply, PMF.pure_map]
    simp [recordedPublicTailLabel, recordedPublicInverseTail, rejected]
    rfl

/-- The complete hash tail writes its two blocks after the success check. -/
theorem recordedPublicHandler_hashTail [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (recordedPublicHandler attempts) (772 + extra) ⟨615, memory⟩ =
      PMF.pure (some (⟨recordedPublicTailLabel memory, (recordedPublicHashTail memory).1⟩,
        (recordedPublicHashTail memory).2)) := by
  rw [show 772 + extra = (771 + extra) + 1 by omega, recordedPublicHandler_hashGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 771 + extra = (770 + extra) + 1 by omega, recordedPublicHandler_abort, PMF.pure_map]
    simp [recordedPublicTailLabel, recordedPublicHashTail, rejected]
    rfl
  · rw [if_neg rejected]
    rw [recordedPublicHandler_hashReply, PMF.pure_map]
    simp [recordedPublicTailLabel, recordedPublicHashTail, rejected]
    rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
