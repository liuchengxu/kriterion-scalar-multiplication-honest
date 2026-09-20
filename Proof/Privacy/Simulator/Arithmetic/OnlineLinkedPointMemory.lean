import Proof.Privacy.Simulator.Arithmetic.PointGateReady
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine

/-- The complete link preserves every prepared point record. -/
theorem encLinkSamples_pointMemory [FieldCertificate]
    (attempts limit : Nat) (memory : Memory) (state : SharedOracleSource) (key : BaseField)
    (rows : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (input : AffineInput) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField)
    (records : PointGateMemory rows input target memory.ram (BitVec.ofNat 256 privateBase))
    (represented : SharedSourceMemory memory state limit)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = []) (result : EncLinkResult)
    (supported : result ∈ (encLinkSamples attempts memory state.family key []).support) :
    PointGateMemory rows input target result.1.1.ram (BitVec.ofNat 256 privateBase) := by
  apply records.privateFrame rows input target memory.ram result.1.1.ram
  intro cell lower upper
  exact encLinkSamples_beforeOutput attempts limit onlineLinkedBase cell memory state.family key []
    represented.family represented.capacity operand outputBase (by decide) (by decide)
    represented.counts.1 represented.counts.2.1 room hashRoom wire
    (by
      have fixed : 256 ≤ privateBase := by decide
      exact le_trans fixed lower)
    (by
      have fixed : privateBase + 834395 ≤ onlineLinkedBase := by decide
      exact lt_of_lt_of_le upper fixed) result supported

/-- The complete link preserves both selected input-coordinate words. -/
theorem encLinkSamples_coordinates [FieldCertificate]
    (attempts limit : Nat) (memory : Memory) (state : SharedOracleSource) (key : BaseField) (input : AffineInput)
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (represented : SharedSourceMemory memory state limit)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = []) (result : EncLinkResult)
    (supported : result ∈ (encLinkSamples attempts memory state.family key []).support) :
    result.1.1.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    result.1.1.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val := by
  have kept (cell : Nat) := encLinkSamples_beforeOutput attempts limit onlineLinkedBase cell memory state.family key []
    represented.family represented.capacity operand outputBase (by decide) (by decide)
    represented.counts.1 represented.counts.2.1 room hashRoom wire
  constructor
  · exact (kept onlineInputBase (by decide) (by decide) result supported).trans coordinates.1
  · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by
      rw [BitVec.ofNat_add]; rfl
    rw [address]
    exact (kept (onlineInputBase + 1) (by decide) (by decide) result supported).trans (address ▸ coordinates.2)

end Kriterion.ArgoMAC.ArithmeticSimulator
