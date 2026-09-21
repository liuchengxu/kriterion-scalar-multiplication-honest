import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFamily
import Proof.Privacy.Simulator.Arithmetic.SharedPublicRecovery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine Security.OperationalOracle
open GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The typed low block has the exact finite value used by the sparse source. -/
theorem publicBlock_finite (word : Word) :
    blockFin (BitVec.ofNat 128 word.toNat) = sparseWordValue (2 ^ 128) (by decide) word := by
  apply Fin.ext
  simp [blockFin, BitVec.equivFin, sparseWordValue]

/-- A typed accepted reply proves that the actual sampler accepted. -/
theorem publicReplyValue_some {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (memory : Memory) (reply : request.Answer) (same : publicReplyValue request memory = some reply) :
    memory.registers 7 ≠ 0#256 ∧ publicAnswerValue request (memory.registers 8) = reply := by
  unfold publicReplyValue at same
  split at same
  · simp at same
  · exact ⟨by assumption, Option.some.inj same⟩

/-- A typed forward reply proves sampler acceptance and the exact overlay output. -/
theorem publicForwardReplyValue_some {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (count : Nat) (memory : Memory) (reply : request.Answer)
    (same : publicForwardReplyValue request count memory = some reply) :
    memory.registers 7 ≠ 0#256 ∧
      publicAnswerValue request ((overlayForwardScan count memory).1.registers 8) = reply := by
  unfold publicForwardReplyValue at same
  split at same
  · simp at same
  · exact ⟨by assumption, Option.some.inj same⟩

/-- The accepted forward observer recovers the exact next permutation from the typed low block. -/
theorem programmedForwardMemoryState_reply (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) (reply : Block)
    (accepted : memory.registers 7 ≠ 0#256)
    (value : BitVec.ofNat 128 ((overlayForwardScan state.overlay.length memory).1.registers 8).toNat = reply) :
    programmedForwardMemoryState state input memory = programmedForwardNext state input (blockFin reply) := by
  unfold programmedForwardMemoryState overlayQueryValue
  rw [if_neg accepted]
  rw [← value, publicBlock_finite]
  rfl

/-- The accepted inverse observer recovers the exact next permutation from the typed low block. -/
theorem programmedInverseMemoryState_reply (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) (reply : Block)
    (accepted : memory.registers 7 ≠ 0#256)
    (value : BitVec.ofNat 128 (memory.registers 8).toNat = reply) :
    programmedInverseMemoryState state input memory = programmedInverseNext state input (blockFin reply) := by
  unfold programmedInverseMemoryState queryValue
  rw [if_neg accepted]
  rw [← value, publicBlock_finite]
  rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator
