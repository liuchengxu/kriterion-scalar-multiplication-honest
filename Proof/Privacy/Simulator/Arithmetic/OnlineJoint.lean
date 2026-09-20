import Proof.Privacy.Simulator.Arithmetic.GateDirectiveSchedule
import Proof.Privacy.Simulator.Arithmetic.GateTypedData
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingSourceJoint
import Proof.Privacy.Simulator.Arithmetic.EncLinkCompleteMemory
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineProtocol
import Proof.Privacy.Simulator.Arithmetic.SharedExactSourceGame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

abbrev OnlineJointMemoryResult := Garbling.Labels × (Memory × Nat) × SharedOracleSource

/-- The curve joint uses the same descriptor and command order as the source schedule. -/
def onlineCurveJoint (attempts : Nat) (request : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateLoopJointResult) :=
  gateLoopCoupled curveGatePlan (fun gate => sharedDirectiveSlot (curveDirectiveAt request input mac gate))
    attempts 1270 0 memory state

/-- The point joint uses all 92 rows in the compiler's descriptor order. -/
def onlinePointJoint (attempts : Nat) (requests : PointGateRequests) (input : AffineInput) (mac : InputMac)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateLoopJointResult) :=
  gateLoopCoupled pointGatePlan (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
    attempts 277368 0 memory state

/-- The valid gate joint retains original labels and both exact instruction charges. -/
def onlineValidGateJoint (attempts : Nat) (frame : Shared.Simulator.State) (input : AffineInput)
    (requests : PointGateRequests) (linked : InputMac) (memory : Memory) (state : SharedOracleSource) :
    PMF (Option OnlineJointMemoryResult) :=
  bindCutoff (onlineCurveJoint attempts (frame.selectedCurve input) input (frame.labels input).inputMac
    (onlineGateInitial memory) state) fun curve =>
    (onlinePointJoint attempts requests input linked (onlinePointGateInitial curve.1.2.1) curve.2).map
      (Option.map fun point =>
        (frame.labels input, (onlineFinalMemory point.1.2.1, curve.1.2.2 + point.1.2.2 + 200672), point.2))

/-- The absent-output joint runs only the curve schedule before final label output. -/
def onlineNullMemoryJoint [FieldCertificate] (attempts : Nat) (frame : Shared.Simulator.State)
    (input : AffineInput) (memory : Memory) (state : SharedOracleSource) : PMF (Option OnlineJointMemoryResult) :=
  (onlineCurveJoint attempts (frame.selectedCurve input) input (frame.labels input).inputMac
    (onlineNullGateInitial (onlineCurveMemory memory input none [])) state).map
    (Option.map fun result => (frame.labels input,
      (onlineFinalMemory (onlineTagMemory result.1.2.1), result.1.2.2 + onlinePrefixCost none + 200672), result.2))

/-- The valid joint samples the exact private coin and retains the actual link memory. -/
def onlineValidMemoryJoint [FieldCertificate] [GroupCertificate] (attempts : Nat)
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Point) (key : BaseField)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option OnlineJointMemoryResult) :=
  let sampledFrom := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  (onlineSamplingMemory attempts sampledFrom).bind fun sampled =>
    let coin := onlineSamplingCoin attempts sampledFrom sampled
    let prepared := onlinePreparedMemory sampled.1 output coin
    (encLinkSamples attempts prepared state.family key []).bind fun linked =>
      if linked.1.2.2 = 7466 then
        (onlineValidGateJoint attempts frame input
          (frame.selectedPoints input output (Vector.ofFn coin.1) coin.2)
          (encLinkOutputMac linked.1.1 onlineLinkedBase) linked.1.1 {state with family := linked.2}).map
          (Option.map fun result =>
            (result.1, (result.2.1.1, result.2.1.2 + linked.1.2.1 + onlinePrepareCost coin + sampled.2 +
              onlinePrefixCost (some output) + 4), result.2.2))
      else PMF.pure none

/-- The complete online joint chooses exactly the machine's output branch. -/
def onlineMemoryJoint [FieldCertificate] [GroupCertificate] (attempts : Nat)
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Option Point)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option OnlineJointMemoryResult) :=
  match output with
  | none => onlineNullMemoryJoint attempts (sharedOfflineFrame coin) input memory state
  | some point => onlineValidMemoryJoint attempts (sharedOfflineFrame coin) input point coin.2.2 memory state

/-- The protocol joint charges the dispatcher and retains the source state for the decision phase. -/
def compiledOnlineJoint [FieldCertificate] [GroupCertificate] (attempts : Nat)
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Option Point)
    (state : State) (source : SharedOracleSource) : PMF (Option (Garbling.Labels × State × SharedOracleSource)) :=
  let memory := compiledOnlineMemory state.memory
    (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output output)
  (onlineMemoryJoint attempts coin input output memory source).map (Option.map fun result =>
    (result.1, (⟨result.2.1.1, state.spent + (result.2.1.2 + 2), state.queries⟩ : State), result.2.2))

end
end Kriterion.ArgoMAC.ArithmeticSimulator
