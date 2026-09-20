import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkLoopFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The complete link preserves every private word before its output buffer. -/
theorem encLinkSamples_beforeOutput [BN254.FieldCertificate]
    (attempts limit output cell : Nat) (memory : Memory) (state : SparseOracleFamily)
    (key : BN254.BaseField) (suffix : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = suffix) (lower : 256 ≤ cell) (earlier : cell < output)
    (result : EncLinkResult) (supported : result ∈ (encLinkSamples attempts memory state key suffix).support) :
    result.1.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨hash, hashMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have ready := encLinkInitialize_ready memory hash.1 hash.2 state key output limit suffix represented capacity
    operand outputBase outputLower outputUpper baseCount overlayCount room hashRoom wire hashMember
  have loop := encLinkLoopSamples_beforeOutput attempts _ suffix encLinkIndices (encLinkScheduled hash.1)
    (encLinkStarted state key hash.1) output limit cell ready lower earlier tail tailMember
  have saved := encLinkSave_state memory
  have family := encLinkSaved_family memory state represented capacity
  have counter : (encLinkSaved memory).ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.hash.length := by
    simpa only [hashWordPairs, List.length_map] using family.hash.count
  have upper : cell < 2 ^ 96 := by omega
  have kept := hashHandlerSamples_private state.hash.length (encLinkSaved memory) hash.1 hash.2 hashMember
    15748 saved.2.1 counter (by omega) cell (by omega) upper
  have ne40 : BitVec.ofNat 256 cell ≠ (40 : Word) := encLinkOutput_separate cell 40 lower upper (by decide)
  have ne39 : BitVec.ofNat 256 cell ≠ (39 : Word) := encLinkOutput_separate cell 39 lower upper (by decide)
  change tail.1.1.ram (BitVec.ofNat 256 cell) = _
  rw [loop, (encLinkScheduled_memory hash.1).1, Function.update_of_ne ne40, Function.update_of_ne ne39,
    kept, encLinkSaved_private memory cell lower upper]

end Kriterion.ArgoMAC.ArithmeticSimulator
