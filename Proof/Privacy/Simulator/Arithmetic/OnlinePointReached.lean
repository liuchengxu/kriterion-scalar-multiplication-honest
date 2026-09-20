import Proof.Privacy.Simulator.Arithmetic.PointGateReady
import Proof.Privacy.Simulator.Arithmetic.OnlineJointFrame
import Proof.Privacy.Simulator.Arithmetic.OnlineCurvePublic

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- The accepted curve loop retains all data for the complete point loop. -/
theorem onlinePointGateInitial_ready [FieldCertificate]
    (attempts limit : Nat) (frame : Shared.Simulator.State) (input : AffineInput)
    (rows : Fin FieldMacToECMac.outputMacCount → RowPublicSample) (target : Fin FieldMacToECMac.outputMacCount → Fin 3 → BaseField)
    (requests : PointGateRequests) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (records : PointGateMemory rows input target memory.ram (BitVec.ofNat 256 privateBase))
    (requestsAt : ∀ row, requests.get row = ⟨(rows row).x.request.retarget input (target row 0),
      (rows row).y.request.retarget input (target row 1), (rows row).z.request.retarget input (target row 2)⟩)
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (BitVec.ofNat 256 onlineLinkedBase) 0
      ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (represented : SharedSourceMemory memory state limit)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineGateInitial memory) state)
    (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110)
    (result : GateLoopJointResult)
    (supported : some result ∈ (onlineCurveJoint attempts (frame.selectedCurve input) input
      (frame.labels input).inputMac (onlineGateInitial memory) state).support) :
    GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
      (fun gate => !(pointDirectiveAt requests input mac gate).bit)
      attempts 277368 0 (limit + 3 * 1270) (onlinePointGateInitial result.1.2.1) result.2 := by
  have firstRam : (onlineGateInitial memory).ram = memory.ram := (onlineOriginalSetup_state memory).1
  have curveRoom : 256 + 2 * (limit + 3 * 1270) < 2 ^ 110 := by
    ring_nf at room ⊢
    omega
  have retained := gateLoopCoupled_memory curveGatePlan _ _ attempts 1270 0 limit
    (onlineGateInitial memory) state (represented.ramEq firstRam) ready curveRoom result supported
  have setup := onlinePointSetup_state (onlineTagMemory result.1.2.1)
  have sourcePointer : (onlinePointGateInitial result.1.2.1).registers 11 = BitVec.ofNat 256 privateBase := setup.2.2.1
  have inputPointer : (onlinePointGateInitial result.1.2.1).registers 12 = BitVec.ofNat 256 onlineInputBase := setup.2.2.2.1
  have labelPointer : (onlinePointGateInitial result.1.2.1).registers 14 = BitVec.ofNat 256 onlineLinkedBase := setup.2.2.2.2
  have pointRam : (onlinePointGateInitial result.1.2.1).ram = result.1.2.1.ram := setup.1
  have same (cell : Nat) (lower : 32 ≤ cell) (upper : cell < 2 ^ 96) :
      (onlinePointGateInitial result.1.2.1).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
    rw [pointRam, retained.2.2 cell lower upper, firstRam]
  apply pointGateMemory_ready attempts (limit + 3 * 1270) rows input target _ mac requests result.2
  · rw [sourcePointer]
    apply records.privateFrame rows input target memory.ram _
    intro cell lower upper
    exact same cell (by
        have fixed : 32 ≤ privateBase := by decide
        exact le_trans fixed lower)
      (by
        have fixed : privateBase + 834395 < 2 ^ 96 := by decide
        exact lt_trans upper fixed)
  · exact requestsAt
  · rw [inputPointer]
    constructor
    · rw [same onlineInputBase (by decide) (by decide)]
      exact coordinates.1
    · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by
        rw [BitVec.ofNat_add]; rfl
      rw [address, same (onlineInputBase + 1) (by decide) (by decide), ← address]
      exact coordinates.2
  · rw [labelPointer]
    intro index inside
    have length : (encLinkMacWords mac).length = 508 := by simp [encLinkMacWords, coordinateBitCount]
    have bound : index < 508 := by simpa only [List.length_map, length] using inside
    simp only [Nat.zero_add]
    rw [← BitVec.ofNat_add, same (onlineLinkedBase + index)]
    · simpa only [Nat.zero_add, BitVec.ofNat_add] using labels index inside
    · have fixed : 32 ≤ onlineLinkedBase := by decide
      exact le_trans fixed (Nat.le_add_right _ _)
    · have fixed : onlineLinkedBase + 508 < 2 ^ 96 := by decide
      exact lt_trans (Nat.add_lt_add_left bound _) fixed
  · exact setup.2.2.1
  · exact setup.2.2.2.1
  · exact setup.2.2.2.2
  · exact retained.1.ramEq pointRam
  · ring_nf at room ⊢
    omega

end
end Kriterion.ArgoMAC.ArithmeticSimulator
