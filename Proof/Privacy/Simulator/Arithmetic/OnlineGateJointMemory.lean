import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineKeyBuffers
import Proof.Privacy.Simulator.Arithmetic.GateLoopJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] onlineCurveJoint onlinePointJoint gateLoopCoupled

private theorem curveRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3 * 1270) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

private theorem pointRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3 * 1270 + 3 * 277368) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

/-- Both valid gate loops retain the source and every private caller word. -/
theorem onlineValidGateJoint_memory [FieldCertificate] (attempts limit : Nat) (frame : Shared.Simulator.State)
    (input : AffineInput) (requests : PointGateRequests) (linked : InputMac) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (curveReady : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineGateInitial memory) state)
    (pointReady : ∀ result, some result ∈
      (onlineCurveJoint attempts (frame.selectedCurve input) input (frame.labels input).inputMac (onlineGateInitial memory) state).support →
      GateLoopCoupledReady pointGatePlan
        (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input linked gate))
        (fun gate => !(pointDirectiveAt requests input linked gate).bit)
        attempts 277368 0 (limit + 3 * 1270) (onlinePointGateInitial result.1.2.1) result.2)
    (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : OnlineJointMemoryResult)
    (member : some result ∈ (onlineValidGateJoint attempts frame input requests linked memory state).support) :
    SharedSourceMemory result.2.1.1 result.2.2 (limit + 835914) ∧
      ∀ cell, 32 ≤ cell → cell < 2 ^ 96 →
        result.2.1.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨curve, curveMember, pointMember⟩ := (mem_support_bindCutoff _ _ _).mp member
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp pointMember
  cases raw with
  | none => simp at same
  | some point =>
    have same := Option.some.inj same
    subst result
    have curveRam : (onlineGateInitial memory).ram = memory.ram := (onlineOriginalSetup_state memory).1
    have curveStored := gateLoopCoupled_memory curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineGateInitial memory) state (represented.ramEq curveRam) curveReady
      (curveRoom limit room) curve (by simpa only [onlineCurveJoint] using curveMember)
    have pointRam : (onlinePointGateInitial curve.1.2.1).ram = curve.1.2.1.ram :=
      (onlinePointSetup_state (onlineTagMemory curve.1.2.1)).1
    have pointStored := gateLoopCoupled_memory pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input linked gate))
      (fun gate => !(pointDirectiveAt requests input linked gate).bit)
      attempts 277368 0 (limit + 3 * 1270) (onlinePointGateInitial curve.1.2.1) curve.2
      (curveStored.1.ramEq pointRam) (pointReady curve curveMember) (pointRoom limit room) point (by simpa only [onlinePointJoint] using reached)
    refine ⟨?_, ?_⟩
    · have finalStored := pointStored.1.ramEq (onlineFinalMemory_ram point.1.2.1)
      have cap : limit + 3 * 1270 + 3 * 277368 = limit + 835914 := by omega
      rw [cap] at finalStored
      exact finalStored
    · intro cell lower upper
      change (onlineFinalMemory point.1.2.1).ram _ = _
      rw [onlineFinalMemory_ram, pointStored.2.2 cell lower upper, pointRam,
        curveStored.2.2 cell lower upper, curveRam]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
