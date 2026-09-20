import Proof.Privacy.Simulator.Arithmetic.OnlineKeyBuffers
import Proof.Privacy.Simulator.Arithmetic.RetargetedGateMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineCurveTyped
import Proof.Privacy.Simulator.Arithmetic.OnlineJointFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section

/-- The actual private preparation retains all five retargeted curve adaptors. -/
theorem onlinePreparedMemory_curveRecord [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (coin : OfflineCoin)
    (input : AffineInput) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    RetargetedGateMemory (coin.1.curve.coefficients, coin.1.curve.tables, coin.1.curve.quotients, coin.1.curve.targets)
      2 (((coin.1.curve.request.retarget input coin.2.2).x7Targets 0))
      (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 privateBase) 834395 := by
  let initial := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  have pointer : initial.registers 10 = BitVec.ofNat 256 onlineSampleBase := by
    simp [initial, onlineSampleInitial, onlineSampleSetup, executeLinear, LinearInstruction.execute]
  have ram : initial.ram = (onlineCurveMemory memory input (some output) []).ram := rfl
  have kept (offset : Nat) (lower : 834395 ≤ offset) (upper : offset < 838213) :=
    onlinePreparedMemory_outsidePoints attempts initial final cost pointer supported output sample offset (Or.inr lower) upper
  refine ⟨?_, ?_, ?_⟩ <;> intro gate bit
  all_goals
    have gateBound := gate.isLt
    have bitBound := bit.isLt
    have original := onlineCurveMemory_gateWords memory input (some output) [] coin stored gate bit
  · exact (kept _ (by omega) (by omega)).trans (by simpa only [ram] using original.1)
  · exact (kept _ (by omega) (by omega)).trans (by simpa only [ram] using original.2.1)
  · exact (kept _ (by omega) (by omega)).trans (by simpa only [ram] using original.2.2)

/-- The reached curve loop reads exact typed records after the private and link phases. -/
theorem onlineLinkedCurve_ready [FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (coin : OfflineCoin) (input : AffineInput) (state : SharedOracleSource)
    (records : RetargetedGateMemory
      (coin.1.curve.coefficients, coin.1.curve.tables, coin.1.curve.quotients, coin.1.curve.targets)
      2 ((coin.1.curve.request.retarget input coin.2.2).x7Targets 0) memory.ram (BitVec.ofNat 256 privateBase) 834395)
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
      ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256)))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineGateInitial memory) state := by
  have setup := onlineOriginalSetup_state memory
  have data (gate : Fin 5) (bit : Fin 254) :
      GateTypedData (onlineGateInitial memory) (curveGateCode gate bit)
        ((coin.1.curve.request.retarget input coin.2.2).actualDirective input (coin.2.1.encodeAffine input) gate bit)
        (coin.1.curve.quotients gate bit) := by
    apply curveGateCode_typed coin.1.curve input coin.2.2 (coin.2.1.encodeAffine input) _ gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.2.1]; exact coordinates
    · rw [onlineGateInitial, setup.1, setup.2.2.2.2]; exact labels
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact records.target gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact records.quotient gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact records.table gate bit
  apply gateLoopCoupledReady_typed curveGatePlan _
    (fun index => coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
      ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩) attempts 1270 0 limit _ _ state
    (by decide) (GatePrivateAgreement.refl _) (represented.ramEq setup.1) room
  · intro index
    simpa only [curveGatePlan, Vector.getElem_ofFn, curveDirectiveAt, onlineGateInitial, sharedOfflineFrame_curve, sharedOfflineFrame_inputMac] using
      data ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩
  · intro index
    simpa only [curveGatePlan, Vector.getElem_ofFn, onlineGateInitial] using curveGateCode_private (onlineGateInitial memory)
      ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩
      onlineOriginalBase setup.2.2.1 setup.2.2.2.1 setup.2.2.2.2 (by decide) (by decide)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
