import Proof.Privacy.Simulator.Arithmetic.OnlineJoint
import Proof.Privacy.Simulator.Arithmetic.SharedOnlineCutoffSource
import Proof.Privacy.Simulator.Arithmetic.GateLoopReadySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- The curve joint has the exact source schedule marginal. -/
theorem onlineCurveJoint_source [FieldCertificate] (attempts limit : Nat)
    (request : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
      (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    (onlineCurveJoint attempts request input mac memory state).map (Option.map fun result => ((), result.2)) =
      sharedCommandListCutoff attempts ((scheduleCommands (request.schedule input mac)).map sharedCommand) state := by
  have source := gateLoopCoupled_source curveGatePlan
    (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
    (fun gate => !(curveDirectiveAt request input mac gate).bit) attempts 1270 0 limit memory state ready room
  rw [sharedDirectiveLoop_list, curveDirectiveAt_schedule] at source
  exact source

/-- The absent-output joint has the exact complete online source marginal. -/
theorem onlineNullMemoryJoint_source [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (frame : Shared.Simulator.State) (input : AffineInput)
    (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineNullGateInitial (onlineCurveMemory memory input none [])) state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    (onlineNullMemoryJoint attempts frame input memory state).map (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff attempts) (sharedOnlineTotalProgram attempts frame input none) state := by
  rw [sharedOnlineTotalProgram_none, ← onlineCurveJoint_source attempts limit _ _ _ _ _ ready room]
  simp only [onlineNullMemoryJoint, PMF.map_comp, Option.map_map, Function.comp_def]

/-- The absent-output joint retains the exact accepted machine memory and charge. -/
theorem onlineNullMemoryJoint_machine [FieldCertificate] (attempts limit : Nat)
    (frame : Shared.Simulator.State) (input : AffineInput) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineNullGateInitial (onlineCurveMemory memory input none [])) state)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256) :
    (onlineNullMemoryJoint attempts frame input memory state).map (Option.map fun result => result.2.1) =
      (compiledOnlineNullSamples attempts memory input []).map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none) := by
  have projected := congrArg (PMF.map (Option.map fun result : Bool × Memory × Nat =>
    (onlineFinalMemory (onlineTagMemory result.2.1), result.2.2 + onlinePrefixCost none + 200672)))
    (gateLoopCoupled_machine curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt (frame.selectedCurve input) input (frame.labels input).inputMac gate).bit)
      attempts 1270 0 limit _ state ready room attemptFits)
  simp only [PMF.map_comp, Option.map_map, Function.comp_def] at projected
  simp only [onlineNullMemoryJoint, PMF.map_comp, Option.map_map, Function.comp_def, onlineCurveJoint]
  rw [projected]
  simp only [compiledOnlineNullSamples, PMF.map_comp, Function.comp_def]
  apply congrArg (fun f => PMF.map f (gateLoopSamples curveGatePlan attempts 1270 0
    (onlineNullGateInitial (onlineCurveMemory memory input none []))))
  funext result
  cases accepted : result.1 <;> simp only [accepted, Bool.false_eq_true, ↓reduceIte,
    Option.map_none, Option.map_some, onlineNullGateResult]
  all_goals simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
