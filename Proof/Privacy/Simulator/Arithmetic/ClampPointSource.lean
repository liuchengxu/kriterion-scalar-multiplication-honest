import Proof.Privacy.Simulator.Arithmetic.ClampPointMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineInputProtocol

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The selected-output decoder reads the exact protocol record. -/
theorem selectedOutputPoint_record [BN254.FieldCertificate] (base : Memory) (x y : Nat) (point : BN254.Point) :
    let words := onlineOutputWords (some point)
    selectedOutputPoint (onlineRecordRam base x y words.1 words.2.1 words.2.2) (base.registers 10) = some point := by
  dsimp only
  apply Eq.trans _ (scalarMultiple_write (fun _ => 0) point)
  apply readPoint_congr <;> cases point <;>
    simp [selectedOutputPoint, onlineRecordRam, onlineOutputWords, scalarMultiple, writePoint]

/-- The online input parser supplies the selected output to the correction machine. -/
theorem selectedOutputPoint_onlineInput [BN254.FieldCertificate] (base : Memory)
    (input : BN254.AffineInput) (point : BN254.Point) (rest : List Bool) :
    selectedOutputPoint (onlineInputMemory base input (some point) rest).ram (base.registers 10) = some point := by
  rw [(onlineInputMemory_values base input (some point) rest).1]
  exact selectedOutputPoint_record base input.x.val input.y.val point

end Kriterion.ArgoMAC.ArithmeticSimulator
