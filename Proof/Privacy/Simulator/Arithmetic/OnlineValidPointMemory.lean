import Proof.Privacy.Simulator.Arithmetic.OnlineLinkedPointMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineJointFrame
import Proof.Privacy.Simulator.Arithmetic.OnlineCurveLabels

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The actual valid prefix establishes every selected point record before the link. -/
theorem onlineValidPrepared_pointMemory [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    let sample := onlineSamplingCoin attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    PointGateMemory (fun row => coin.1.points.get row) input (onlineTargetField output sample)
      (onlinePreparedMemory sampled.1 output sample).ram (BitVec.ofNat 256 privateBase) := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin attempts base sampled
  have pointer : base.registers 10 = BitVec.ofNat 256 onlineSampleBase := by
    simp [base, onlineSampleInitial, onlineSampleSetup, executeLinear, LinearInstruction.execute]
  have ram : base.ram = (onlineCurveMemory memory input (some output) []).ram := rfl
  apply onlinePreparedMemory_pointRecords attempts base sampled.1 sampled.2 pointer supported input output sample
    (fun row => coin.1.points.get row)
  · rw [ram]
    exact onlineCurveMemory_pointRows memory input (some output) [] coin stored
  · rw [ram]
    exact onlineCurveMemory_coordinates memory input (some output) []

end Kriterion.ArgoMAC.ArithmeticSimulator
