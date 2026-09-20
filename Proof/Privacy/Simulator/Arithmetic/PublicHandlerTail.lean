import Proof.Privacy.Simulator.Arithmetic.PublicHandlerOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward tail either aborts or applies the overlay and emits one block. -/
def publicForwardTail (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else
    let scanned := overlayForwardScan count memory
    (executeLinear (wordOutput 128) scanned.1, scanned.2 + 386)

/-- The inverse tail either aborts or emits its one-block answer. -/
def publicInverseTail (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else (executeLinear (wordOutput 128) memory, 386)

/-- The hash tail either aborts or emits its two-block answer. -/
def publicHashTail (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 2)
  else (executeLinear hashOutput memory, 772)

/-- The final label records whether the handler returned a wire answer. -/
def publicTailLabel (memory : Memory) : Fin 1772 :=
  if memory.registers 7 = 0#256 then 1771 else 1770

/-- The complete forward tail includes its flag check, overlay scan, output, and halt. -/
theorem publicHandler_forwardTail [BN254.FieldCertificate] (attempts count extra : Nat)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 count) :
    run (publicHandler attempts) (11 * count + 393 + extra) ⟨280, memory⟩ =
      PMF.pure (some (⟨publicTailLabel memory, (publicForwardTail count memory).1⟩,
        (publicForwardTail count memory).2)) := by
  rw [show 11 * count + 393 + extra = (11 * count + 392 + extra) + 1 by omega,
    publicHandler_forwardGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 11 * count + 392 + extra = (11 * count + 391 + extra) + 1 by omega,
      publicHandler_abort, PMF.pure_map]
    simp [publicTailLabel, publicForwardTail, rejected]
    rfl
  · rw [if_neg rejected]
    have bound := overlayForward_cost count memory
    let remaining := 11 * count + 392 + extra - (overlayForwardScan count memory).2
    have enough : 385 ≤ remaining := by dsimp [remaining]; omega
    have scanned := overlayForward_continue (publicHandler attempts) publicOverlayLoadLabels publicOverlayScanLabels
      (publicHandler_overlayLoad attempts) (publicHandler_overlayScan attempts) rfl count memory fits counter remaining
    change run (publicHandler attempts) _ ⟨281, memory⟩ = _ at scanned
    have reserve : 11 * count + 392 + extra = (overlayForwardScan count memory).2 + remaining := by
      dsimp [remaining]; omega
    rw [reserve, scanned]
    change ((run (publicHandler attempts) remaining
      ⟨616, (overlayForwardScan count memory).1⟩).map _).map _ = _
    rw [show remaining = 385 + (remaining - 385) by omega, publicHandler_blockReply,
      PMF.pure_map, PMF.pure_map]
    simp [publicForwardTail, publicTailLabel, rejected, Nat.add_assoc, Nat.add_comm]
    rw [← Nat.add_assoc]
    rfl

/-- The complete inverse tail rejects a cutoff result before it writes any bits. -/
theorem publicHandler_inverseTail [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (publicHandler attempts) (386 + extra) ⟨541, memory⟩ =
      PMF.pure (some (⟨publicTailLabel memory, (publicInverseTail memory).1⟩,
        (publicInverseTail memory).2)) := by
  rw [show 386 + extra = (385 + extra) + 1 by omega, publicHandler_inverseGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 385 + extra = (384 + extra) + 1 by omega, publicHandler_abort, PMF.pure_map]
    simp [publicTailLabel, publicInverseTail, rejected]
    rfl
  · rw [if_neg rejected]
    rw [publicHandler_blockReply, PMF.pure_map]
    simp [publicTailLabel, publicInverseTail, rejected]
    rfl

/-- The complete hash tail writes its two blocks after the success check. -/
theorem publicHandler_hashTail [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (publicHandler attempts) (772 + extra) ⟨615, memory⟩ =
      PMF.pure (some (⟨publicTailLabel memory, (publicHashTail memory).1⟩,
        (publicHashTail memory).2)) := by
  rw [show 772 + extra = (771 + extra) + 1 by omega, publicHandler_hashGate]
  by_cases rejected : memory.registers 7 = 0#256
  · rw [if_pos rejected]
    rw [show 771 + extra = (770 + extra) + 1 by omega, publicHandler_abort, PMF.pure_map]
    simp [publicTailLabel, publicHashTail, rejected]
    rfl
  · rw [if_neg rejected]
    rw [publicHandler_hashReply, PMF.pure_map]
    simp [publicTailLabel, publicHashTail, rejected]
    rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
