import Proof.Privacy.Simulator.Arithmetic.OnlineGateJointMemory
import Proof.Privacy.Simulator.Arithmetic.GateLoopBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] onlineCurveJoint onlinePointJoint gateLoopCoupled gateLoopSamples

/-- Each accepted curve joint retains an actual gate-loop sample. -/
private theorem validCurveJoint_actual [FieldCertificate] (attempts limit : Nat)
    (request : CurveGateRequest) (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
      (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : GateLoopJointResult)
    (supported : some result ∈ (onlineCurveJoint attempts request input mac memory state).support) :
    result.1 ∈ (gateLoopSamples curveGatePlan attempts 1270 0 memory).support := by
  have projected : some result.1 ∈ ((onlineCurveJoint attempts request input mac memory state).map
      (Option.map Prod.fst)).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, supported, rfl⟩
  rw [onlineCurveJoint_machine attempts limit request input mac memory state ready room attemptFits] at projected
  obtain ⟨actual, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  split at same
  · have equal := Option.some.inj same
    rw [← equal]
    exact member
  · cases same

/-- Each accepted point joint retains an actual loop sample. -/
theorem onlinePointJoint_actual [FieldCertificate] (attempts limit : Nat)
    (requests : PointGateRequests) (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
      (fun gate => !(pointDirectiveAt requests input mac gate).bit) attempts 277368 0 limit memory state)
    (room : 256 + 2 * (limit + 3 * 277368) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (result : GateLoopJointResult)
    (supported : some result ∈ (onlinePointJoint attempts requests input mac memory state).support) :
    result.1 ∈ (gateLoopSamples pointGatePlan attempts 277368 0 memory).support := by
  have projected : some result.1 ∈ ((onlinePointJoint attempts requests input mac memory state).map
      (Option.map Prod.fst)).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨some result, supported, rfl⟩
  rw [onlinePointJoint_machine attempts limit requests input mac memory state ready room attemptFits] at projected
  obtain ⟨actual, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  split at same
  · have equal := Option.some.inj same
    rw [← equal]
    exact member
  · cases same

/-- Both valid gate loops retain the keys and emit their exact selected labels. -/
theorem onlineValidGateJoint_keyProtocol [FieldCertificate] (attempts limit : Nat) (frame : Shared.Simulator.State)
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
    (key : InputMacKey)
    (keyEq : (frame.labels input).inputMac = key.encodeAffine input)
    (keys : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words key))
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (empty : memory.bits 3 = [])
    (result : OnlineJointMemoryResult)
    (member : some result ∈ (onlineValidGateJoint attempts frame input requests linked memory state).support) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.2.1.1.bits 3) =
      some (Lamport.selectedLabels result.1.inputMac) := by
  have retained := (onlineValidGateJoint_memory attempts limit frame input requests linked memory state
    represented curveReady pointReady room attemptFits result member).2
  obtain ⟨curve, curveMember, pointMember⟩ := (mem_support_bindCutoff _ _ _).mp member
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp pointMember
  cases raw with
  | none => simp at same
  | some point =>
    have same := Option.some.inj same
    subst result
    have curveRoom : 256 + 2 * (limit + 3810) < 2 ^ 110 := by ring_nf at room ⊢; omega
    have pointRoom : 256 + 2 * (limit + 3 * 1270 + 3 * 277368) < 2 ^ 110 := by ring_nf at room ⊢; omega
    have curveActual := validCurveJoint_actual attempts limit _ _ _ _ state curveReady curveRoom attemptFits curve curveMember
    have pointActual := onlinePointJoint_actual attempts (limit + 3 * 1270) _ _ _ _ curve.2
      (pointReady curve curveMember) pointRoom attemptFits point reached
    have curveBits := gateLoopSamples_bits curveGatePlan attempts 1270 0 _ curve.1 curveActual
    have pointBits := gateLoopSamples_bits pointGatePlan attempts 277368 0 _ point.1 pointActual
    have privateFrame : ∀ cell, 32 ≤ cell → cell < 2 ^ 96 →
        point.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
      simpa only [onlineFinalMemory_ram] using retained
    change GarbledCircuit.SimulatorProtocol.words 128 508 ((onlineFinalMemory point.1.2.1).bits 3) = _
    rw [keyEq]
    apply onlineFinalMemory_keyProtocol _ key input
    · intro index inside
      have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
      rw [← BitVec.ofNat_add, privateFrame (privateBase + (1 + index)) (by unfold privateBase; omega)
        (by unfold privateBase; omega)]
      simpa only [BitVec.ofNat_add] using keys index inside
    · constructor
      · rw [privateFrame onlineInputBase (by decide) (by decide)]
        exact coordinates.1
      · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by
          rw [BitVec.ofNat_add]; rfl
        rw [address, privateFrame (onlineInputBase + 1) (by decide) (by decide), ← address]
        exact coordinates.2
    · rw [pointBits]
      change (executeLinear onlinePointSetup (onlineTagMemory curve.1.2.1)).bits 3 = []
      rw [(onlinePointSetup_state _).2.1]
      change curve.1.2.1.bits 3 = []
      rw [curveBits]
      change (executeLinear onlineOriginalSetup memory).bits 3 = []
      rw [(onlineOriginalSetup_state _).2.1, empty]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
