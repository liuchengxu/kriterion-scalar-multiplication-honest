import Proof.Privacy.Simulator.Arithmetic.EncLinkOutputWords
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SimulatorMachine

/-- Every accepted complete link retains its source family and full widened output array. -/
theorem encLinkSamples_memory [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField)
    (inputBase output limit : Nat) (suffix : List Bool) (labels : Fin 508 → Block)
    (x y : BitVec coordinateBitCount)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = x.setWidth 256) (inputY : memory.registers 13 = y.setWidth 256)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0 (List.ofFn fun index => (labels index).setWidth 256))
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110) (wire : memory.bits 0 = suffix)
    (result : EncLinkResult) (supported : result ∈ (encLinkSamples attempts memory state key suffix).support)
    (accepted : result.1.2.2 ≠ 7467) :
    OracleFamilyMemory result.1.1.ram result.2 ∧ OracleFamilyFits result.2 ∧
      result.1.2.2 = 7466 ∧ result.1.1.bits 0 = suffix ∧
      WordsAt result.1.1.ram (BitVec.ofNat 256 output) 0
        ((encLinkMacWords (encLinkOutputMac result.1.1 output)).map (fun label => label.setWidth 256)) := by
  obtain ⟨hash, hashMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have ready := encLinkInitialize_ready memory hash.1 hash.2 state key output limit suffix
    represented capacity operand outputBase outputLower outputUpper baseCount overlayCount room hashRoom wire hashMember
  have data := encLinkInitialize_data memory hash.1 hash.2 state inputBase labels x y represented capacity hashRoom
    inputPointer inputX inputY inputLower inputUpper stored hashMember
  have outputWords := encLinkLoopSamples_wordsAt attempts _ _ x y labels (encLinkScheduled hash.1)
    (encLinkStarted state key hash.1) suffix inputBase output limit ready data inputLower inputUpper separate tail tailMember accepted
  have memoryLaw := encLinkLoopSamples_memory attempts _ suffix encLinkIndices (encLinkScheduled hash.1)
    (encLinkStarted state key hash.1) output limit ready tail tailMember
  exact ⟨memoryLaw.1, memoryLaw.2.1, ((memoryLaw.2.2.resolve_left accepted).1),
    (memoryLaw.2.2.resolve_left accepted).2.1, outputWords⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
