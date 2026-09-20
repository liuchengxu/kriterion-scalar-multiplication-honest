import Proof.Privacy.Simulator.Arithmetic.OnlineNullJointSource
import Proof.Privacy.Simulator.Arithmetic.SharedGateLoopCommands

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

attribute [local irreducible] onlineCurveJoint onlinePointJoint onlineValidGateJoint gateLoopCoupled

private theorem pointRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3 * 1270 + 3 * 277368) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

private theorem curveRoom (limit : Nat) (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    256 + 2 * (limit + 3810) < 2 ^ 110 := by
  ring_nf at room ⊢
  omega

/-- The point joint has the exact source command-list marginal. -/
theorem onlinePointJoint_source [FieldCertificate] (attempts limit : Nat) (requests : PointGateRequests)
    (input : AffineInput) (mac : InputMac) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
      (fun gate => !(pointDirectiveAt requests input mac gate).bit) attempts 277368 0 limit memory state)
    (room : 256 + 2 * (limit + 3 * 277368) < 2 ^ 110) :
    (onlinePointJoint attempts requests input mac memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts ((scheduleCommands (pointGateSchedule requests input mac)).map sharedCommand) state := by
  simpa only [onlinePointJoint, sharedDirectiveLoop_list, pointDirectiveAt_schedule] using
    gateLoopCoupled_source pointGatePlan _ _ attempts 277368 0 limit memory state ready room

/-- Both valid gate phases have the exact combined source schedule. -/
theorem onlineValidGateJoint_source [FieldCertificate] (attempts limit : Nat) (frame : Shared.Simulator.State)
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
    (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110) :
    (onlineValidGateJoint attempts frame input requests linked memory state).map
      (Option.map fun result => (result.1, result.2.2)) =
      (sharedCommandListCutoff attempts
        ((scheduleCommands (pipelineGateSchedule (frame.selectedCurve input) requests input (frame.labels input).inputMac linked)).map sharedCommand)
        state).map (Option.map fun result => (frame.labels input, result.2)) := by
  unfold onlineValidGateJoint
  have projected := cutoff_map_bind
    (onlineCurveJoint attempts (frame.selectedCurve input) input (frame.labels input).inputMac (onlineGateInitial memory) state)
    (fun curve => (onlinePointJoint attempts requests input linked (onlinePointGateInitial curve.1.2.1) curve.2).map
      (Option.map fun point => (frame.labels input, (onlineFinalMemory point.1.2.1, curve.1.2.2 + point.1.2.2 + 200672), point.2)))
    (fun result => ((), result.2)) (fun result : OnlineJointMemoryResult => (result.1, result.2.2))
    (fun result => (sharedCommandListCutoff attempts ((scheduleCommands (pointGateSchedule requests input linked)).map sharedCommand) result.2).map
      (Option.map fun result => (frame.labels input, result.2))) (by
      intro curve supported
      have law := onlinePointJoint_source attempts (limit + 3 * 1270) requests input linked
        (onlinePointGateInitial curve.1.2.1) curve.2 (pointReady curve supported) (pointRoom limit room)
      have mapped := congrArg (PMF.map (Option.map fun result : Unit × SharedOracleSource => (frame.labels input, result.2))) law
      simpa only [PMF.map_comp, Option.map_map, Function.comp_def] using mapped)
  rw [projected, onlineCurveJoint_source attempts limit _ _ _ _ _ curveReady (curveRoom limit room)]
  simp only [pipelineGateSchedule, scheduleCommands, List.flatMap_append, List.map_append,
    sharedCommandListCutoff_append, bindCutoff, PMF.map_bind]
  congr 1
  funext result
  cases result <;> simp only [PMF.pure_map, Option.map_none]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
