import Proof.Privacy.Simulator.Arithmetic.OnlineJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] onlineCurveJoint onlinePointJoint onlineValidGateJoint gateLoopCoupled gateLoopSamples

private theorem pointRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3 * 1270 + 3 * 277368) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

private theorem curveRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3 * 1270) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

/-- The curve joint retains the actual loop result and instruction charge. -/
theorem onlineCurveJoint_machine [FieldCertificate] (attempts limit : Nat) (request : CurveGateRequest)
    (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
      (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state)
    (room : 256 + 2 * (limit + 3 * 1270) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (onlineCurveJoint attempts request input mac memory state).map (Option.map Prod.fst) =
      (gateLoopSamples curveGatePlan attempts 1270 0 memory).map (fun result => if result.1 then some result else none) := by
  simpa only [onlineCurveJoint] using gateLoopCoupled_machine curveGatePlan _ _ attempts 1270 0 limit memory state ready room attemptFits

/-- The point joint retains the actual loop result and instruction charge. -/
theorem onlinePointJoint_machine [FieldCertificate] (attempts limit : Nat) (requests : PointGateRequests)
    (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
      (fun gate => !(pointDirectiveAt requests input mac gate).bit) attempts 277368 0 limit memory state)
    (room : 256 + 2 * (limit + 3 * 277368) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (onlinePointJoint attempts requests input mac memory state).map (Option.map Prod.fst) =
      (gateLoopSamples pointGatePlan attempts 277368 0 memory).map (fun result => if result.1 then some result else none) := by
  simpa only [onlinePointJoint] using gateLoopCoupled_machine pointGatePlan _ _ attempts 277368 0 limit memory state ready room attemptFits

/-- Both valid gate phases retain the exact actual memory and complete instruction charge. -/
theorem onlineValidGateJoint_machine [FieldCertificate] (attempts limit : Nat) (frame : Shared.Simulator.State)
    (input : AffineInput) (requests : PointGateRequests) (linked : InputMac) (memory : Memory) (state : SharedOracleSource)
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
    (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (onlineValidGateJoint attempts frame input requests linked memory state).map
      (Option.map fun result => result.2.1) =
      (onlineGateSamples attempts memory).map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none) := by
  unfold onlineValidGateJoint
  let charged (curve : Bool × Memory × Nat) :=
    (gateLoopSamples pointGatePlan attempts 277368 0 (onlinePointGateInitial curve.2.1)).map
      (fun point => if point.1 then some (onlineFinalMemory point.2.1, curve.2.2 + point.2.2 + 200672) else none)
  have projected := cutoff_map_bind
    (onlineCurveJoint attempts (frame.selectedCurve input) input (frame.labels input).inputMac (onlineGateInitial memory) state)
    (fun curve => (onlinePointJoint attempts requests input linked (onlinePointGateInitial curve.1.2.1) curve.2).map
      (Option.map fun point => (frame.labels input, (onlineFinalMemory point.1.2.1, curve.1.2.2 + point.1.2.2 + 200672), point.2)))
    Prod.fst (fun result : OnlineJointMemoryResult => result.2.1) charged (by
      intro curve member
      have law := onlinePointJoint_machine attempts (limit + 3 * 1270) requests input linked
        (onlinePointGateInitial curve.1.2.1) curve.2 (pointReady curve member) (pointRoom limit room) attemptFits
      have mapped := congrArg (PMF.map (Option.map fun point : Bool × Memory × Nat =>
        (onlineFinalMemory point.2.1, curve.1.2.2 + point.2.2 + 200672))) law
      simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
      rw [mapped]
      apply congrArg (fun f => PMF.map f (gateLoopSamples pointGatePlan attempts 277368 0 (onlinePointGateInitial curve.1.2.1)))
      funext point
      cases point.1 <;> rfl)
  rw [projected]
  rw [onlineCurveJoint_machine attempts limit (frame.selectedCurve input) input (frame.labels input).inputMac
    (onlineGateInitial memory) state curveReady (curveRoom limit room) attemptFits]
  simp only [bindCutoff, PMF.bind_map, onlineGateSamples, onlineCurvePointSamples, PMF.map_comp, PMF.map_bind,
    Function.comp_def]
  apply ThreePhase.bind_eq_on_support
  intro curve member
  cases normal : curve.1 with
  | false => simp only [normal, Bool.false_eq_true, ↓reduceIte, onlineAfterCurveSamples, PMF.pure_map]; rfl
  | true =>
      simp only [normal, ↓reduceIte, onlineAfterCurveSamples, onlinePointBranchSamples, PMF.map_comp,
        Function.comp_def, charged]
      apply congrArg (fun f => PMF.map f (gateLoopSamples pointGatePlan attempts 277368 0 (onlinePointGateInitial curve.2.1)))
      funext point
      cases success : point.1 <;>
        simp only [onlinePointGateResult, success, Bool.false_eq_true, ↓reduceIte]
      · rfl
      · congr 2 <;> omega

end
end Kriterion.ArgoMAC.ArithmeticSimulator
