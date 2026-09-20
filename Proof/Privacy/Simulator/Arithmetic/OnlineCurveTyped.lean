import Proof.Privacy.Simulator.Arithmetic.OnlineCurveLabels
import Proof.Privacy.Simulator.Arithmetic.OnlineNullJointSource
import Proof.Privacy.Simulator.Arithmetic.GatePrivateBounds

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine

/-- The final original-label setup exposes each exact curve directive. -/
theorem onlineCurveInitial_typed [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (gate : Fin 5) (bit : Fin 254) :
    GateTypedData (onlineNullGateInitial (onlineCurveMemory memory input output rest)) (curveGateCode gate bit)
      (((sharedOfflineFrame coin).selectedCurve input).actualDirective input
        ((sharedOfflineFrame coin).labels input).inputMac gate bit) (coin.1.curve.quotients gate bit) := by
  let initial := onlineNullGateInitial (onlineCurveMemory memory input output rest)
  have setup := onlineOriginalSetup_state (onlineTagMemory (onlineCurveMemory memory input output rest))
  have ram : initial.ram = (onlineCurveMemory memory input output rest).ram := setup.1
  have pointers : initial.registers 11 = BitVec.ofNat 256 privateBase ∧
      initial.registers 12 = BitVec.ofNat 256 onlineInputBase ∧
      initial.registers 14 = BitVec.ofNat 256 onlineOriginalBase := ⟨setup.2.2.1, setup.2.2.2.1, setup.2.2.2.2⟩
  change GateTypedData initial (curveGateCode gate bit)
    ((coin.1.curve.request.retarget input coin.2.2).actualDirective input (coin.2.1.encodeAffine input) gate bit) _
  have words := onlineCurveMemory_gateWords memory input output rest coin stored gate bit
  apply curveGateCode_typed coin.1.curve input coin.2.2 (coin.2.1.encodeAffine input) initial gate bit
  · rw [ram, pointers.2.1]
    exact onlineCurveMemory_coordinates memory input output rest
  · rw [ram, pointers.2.2]
    exact onlineCurveMemory_labels memory input output rest coin stored
  · rw [ram, pointers.1]
    exact words.1
  · rw [ram, pointers.1]
    exact words.2.1
  · rw [ram, pointers.1]
    exact words.2.2

/-- Each flat curve descriptor reads its exact retargeted directive. -/
theorem onlineCurveInitial_plan [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (index : Fin 1270) :
    GateTypedData (onlineNullGateInitial (onlineCurveMemory memory input output rest)) curveGatePlan[index.val]
      (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input) input
        ((sharedOfflineFrame coin).labels input).inputMac index)
      (coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
        ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩) := by
  simpa only [curveGatePlan, Vector.getElem_ofFn, curveDirectiveAt] using
    onlineCurveInitial_typed memory input output rest coin stored
      ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩

/-- Every flat curve descriptor reads only bounded private addresses. -/
theorem onlineCurveInitial_private [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (index : Fin 1270) :
    GatePrivateAddresses (onlineNullGateInitial (onlineCurveMemory memory input output rest)) curveGatePlan[index.val] := by
  have setup := onlineOriginalSetup_state (onlineTagMemory (onlineCurveMemory memory input output rest))
  simpa only [curveGatePlan, Vector.getElem_ofFn] using curveGateCode_private
    (onlineNullGateInitial (onlineCurveMemory memory input output rest))
    ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩
    onlineOriginalBase setup.2.2.1 setup.2.2.2.1 setup.2.2.2.2 (by decide) (by decide)

/-- The actual common prefix supplies every typed curve-loop command. -/
theorem onlineCurveInitial_ready [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (output : Option Point) (rest : List Bool)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory (onlineNullGateInitial (onlineCurveMemory memory input output rest)) state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineNullGateInitial (onlineCurveMemory memory input output rest)) state := by
  apply gateLoopCoupledReady_typed curveGatePlan _
    (fun index => coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
      ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩) attempts 1270 0 limit _ _ state
    (by decide) (GatePrivateAgreement.refl _) represented room
  · exact onlineCurveInitial_plan memory input output rest coin stored
  · exact onlineCurveInitial_private memory input output rest

end Kriterion.ArgoMAC.ArithmeticSimulator
