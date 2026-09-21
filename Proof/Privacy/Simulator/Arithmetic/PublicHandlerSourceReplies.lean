import Proof.Privacy.Simulator.Arithmetic.ProgrammedForwardJoint
import Proof.Privacy.Simulator.Arithmetic.ProgrammedInverseSource
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTyped
import Proof.Privacy.Simulator.Arithmetic.HashSourceMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security.OperationalOracle

/-- The typed forward observer only converts its accepted word reply. -/
theorem publicForwardReplyValue_word {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (count : Nat) (memory : Memory) :
    publicForwardReplyValue request count memory = (overlayQueryValue count memory).map (publicAnswerValue request) := by
  unfold publicForwardReplyValue overlayQueryValue
  split <;> rfl

/-- The typed base observer only converts its accepted word reply. -/
theorem publicReplyValue_word {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (memory : Memory) :
    publicReplyValue request memory = (queryValue memory).map (publicAnswerValue request) := by
  unfold publicReplyValue queryValue
  split <;> rfl

/-- The typed forward reply has the exact programmed source law. -/
theorem programmedForwardReplies_typed [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedForwardSamples attempts state.base.used memory).map
      (fun result => publicForwardReplyValue request state.overlay.length result.1) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => publicAnswerValue request (BitVec.ofNat 256 result.1.val)) := by
  have source := programmedForwardSamples_wordReply attempts memory oracle state input represented index operand fits overlayFits
  have typed := congrArg (PMF.map (Option.map (publicAnswerValue request))) source
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, publicForwardReplyValue_word] using typed

/-- The typed inverse reply has the exact programmed source law. -/
theorem programmedInverseReplies_typed [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedInverseSamples attempts state.base.used (publicInversePrepared state.overlay.length memory)).map
      (fun result => publicReplyValue request result.1) =
      (drawCutoffLaw attempts (state.inverse input)).map
        (Option.map fun result => publicAnswerValue request (BitVec.ofNat 256 result.1.val)) := by
  have source := programmedInverseSamples_wordReply attempts memory oracle state input represented index operand fits overlayFits
  have typed := congrArg (PMF.map (Option.map (publicAnswerValue request))) source
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, publicReplyValue_word] using typed

/-- Every supported hash sample has its success flag set. -/
theorem hashHandlerSamples_accepted (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support) : final.registers 7 = 1#256 := by
  have reached : final.registers 7 ∈
      ((hashHandlerSamples count memory).map (fun result => result.1.registers 7)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, rfl⟩
  have success : (hashHandlerSamples count memory).map (fun result => result.1.registers 7) =
      PMF.pure (1#256 : Word) := by
    simpa only [hashHandlerSamples, PMF.map_comp, Function.comp_def] using hashTailSamples_success (hashScan count memory).1
  rw [success] at reached
  exact (PMF.mem_support_pure_iff _ _).mp reached

/-- The typed hash reply has the exact source law without a cutoff failure. -/
theorem hashReplies_typed (pairs : HashTable BN254.BaseField (2 ^ 256)) (key : BN254.BaseField)
    (memory : Memory) (oracle : Fin 15749)
    (represented : HashMemory memory.ram oracle (hashWordPairs (fun value => BitVec.ofNat 256 value.val) pairs))
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 key.val) (fits : 2 * pairs.length ≤ 2 ^ 110) :
    (hashHandlerSamples pairs.length memory).map
      (fun result => publicReplyValue (PublicQuery.hash (FixedIndex := Shared.FixedKeyIndex)
        (EncIndex := EncPRF.PermutationIndex) key) result.1) =
      (pairs.query (by decide) key).distribution.map
        (fun result => some (Security.SimulatorMachine.hashFin.symm result.1)) := by
  have joint := hashHandlerSamples_joint (fun value : BN254.BaseField => BitVec.ofNat 256 value.val)
    hashKeyWord_injective pairs key memory oracle represented index operand fits
  have typed := congrArg (PMF.map (fun result => some (Security.SimulatorMachine.hashFin.symm result.1))) joint
  simp only [PMF.map_comp, Function.comp_def] at typed
  rw [← typed]
  apply publicReply_map
  intro result supported
  have accepted := hashHandlerSamples_accepted pairs.length memory result.1 result.2 supported
  simp only [publicReplyValue, accepted, show (1#256 : Word) ≠ 0#256 by decide, if_false, publicAnswerValue]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
