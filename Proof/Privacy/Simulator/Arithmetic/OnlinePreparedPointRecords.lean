import Proof.Privacy.Simulator.Arithmetic.RetargetedGateMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineRetargetBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The actual preparation stores all three retargeted gate records in every point row. -/
theorem onlinePreparedMemory_pointRecords [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (input : AffineInput) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (rows : Fin FieldMacToECMac.outputMacCount → RowPublicSample)
    (stored : ∀ row, WordsAt memory.ram (BitVec.ofNat 256 privateBase)
      (1017 + 9158 * row.val) (rowSchedule.words (rows row)))
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (row : Fin FieldMacToECMac.outputMacCount) :
    let ram := (onlinePreparedMemory final output sample).ram
    RetargetedGateMemory ((rows row).x.coefficients, (rows row).x.tables, (rows row).x.quotients, (rows row).x.targets)
      3 (((rows row).x.request.retarget input (onlineTargetField output sample row 0)).x9Targets 0)
      ram (BitVec.ofNat 256 privateBase) (1017 + 9158 * row.val + 6105) ∧
    RetargetedGateMemory ((rows row).y.coefficients, (rows row).y.tables, (rows row).y.quotients, (rows row).y.targets)
      2 (((rows row).y.request.retarget input (onlineTargetField output sample row 1)).x9Targets 0)
      ram (BitVec.ofNat 256 privateBase) (1017 + 9158 * row.val + 3815) ∧
    RetargetedGateMemory ((rows row).z.coefficients, (rows row).z.tables, (rows row).z.quotients, (rows row).z.targets)
      4 (((rows row).z.request.retarget input (onlineTargetField output sample row 2)).x9Targets 0)
      ram (BitVec.ofNat 256 privateBase) (1017 + 9158 * row.val) := by
  let prepared := executeLinear onlineRetargetSetup (onlineTargetMemory final output sample)
  have ready := onlineRetargetSetup_ready attempts memory final cost pointer supported input output sample rows stored coordinates
  have ram := retargetPointCode_ram rows input prepared (onlineTargetField output sample)
    ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
  have records := pointRetargetFold_records rows input (onlineTargetField output sample)
    (prepared.registers 11) prepared.ram ready.1 row
  have source : prepared.registers 11 = BitVec.ofNat 256 privateBase :=
    (onlineRetargetSetup_state (onlineTargetMemory final output sample)).2.2.1
  dsimp only [onlinePreparedMemory]
  rw [(onlineLinkSetup_state _).1, ram]
  simpa only [source] using records

end Kriterion.ArgoMAC.ArithmeticSimulator
