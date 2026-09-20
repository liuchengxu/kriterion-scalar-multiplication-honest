import Proof.Privacy.Simulator.Arithmetic.OnlineValidLinkReady
import Proof.Privacy.Simulator.Arithmetic.OnlineValidPointMemory
import Proof.Privacy.Simulator.Arithmetic.OnlinePointReached
import Proof.Privacy.Simulator.Arithmetic.OnlinePreparedCurveRecord
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section

private theorem curveRecordOffset (offset : Nat) (bound : offset < 3 * 5 * 254) :
    834395 + offset < 839355 := by omega

/-- The linked memory stores every operand for both gate phases. -/
structure OnlineLinkedGateMemory [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (input : AffineInput) (output : Point)
    (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) (memory : Memory)
    (state : SharedOracleSource) (limit : Nat) : Prop where
  represented : SharedSourceMemory memory state limit
  curve : RetargetedGateMemory
    (coin.1.curve.coefficients, coin.1.curve.tables, coin.1.curve.quotients, coin.1.curve.targets)
    2 ((coin.1.curve.request.retarget input coin.2.2).x7Targets 0) memory.ram (BitVec.ofNat 256 privateBase) 834395
  points : PointGateMemory (fun row => coin.1.points.get row) input (onlineTargetField output sample)
    memory.ram (BitVec.ofNat 256 privateBase)
  coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val
  tag : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0
  originalLabels : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256))
  linkedLabels : WordsAt memory.ram (BitVec.ofNat 256 onlineLinkedBase) 0
    ((encLinkMacWords (encLinkOutputMac memory onlineLinkedBase)).map (fun label => label.setWidth 256))

/-- The linked memory establishes the complete curve-loop invariant. -/
theorem OnlineLinkedGateMemory.curveReady [FieldCertificate] [GroupCertificate]
    (attempts : Nat) {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {memory : Memory}
    {state : SharedOracleSource} {limit : Nat}
    (ready : OnlineLinkedGateMemory coin input output sample memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineGateInitial memory) state :=
  onlineLinkedCurve_ready attempts limit memory coin input state ready.curve ready.coordinates ready.originalLabels ready.represented room

/-- Each accepted curve result establishes the complete point-loop invariant. -/
theorem OnlineLinkedGateMemory.pointReady [FieldCertificate] [GroupCertificate]
    (attempts : Nat) {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {memory : Memory}
    {state : SharedOracleSource} {limit : Nat}
    (ready : OnlineLinkedGateMemory coin input output sample memory state limit)
    (room : 256 + 2 * (limit + 3 * 278638) < 2 ^ 110)
    (result : GateLoopJointResult)
    (supported : some result ∈ (onlineCurveJoint attempts ((sharedOfflineFrame coin).selectedCurve input) input
      ((sharedOfflineFrame coin).labels input).inputMac (onlineGateInitial memory) state).support) :
    GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt
        ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2) input
        (encLinkOutputMac memory onlineLinkedBase) gate))
      (fun gate => !(pointDirectiveAt
        ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2) input
        (encLinkOutputMac memory onlineLinkedBase) gate).bit)
      attempts 277368 0 (limit + 3 * 1270) (onlinePointGateInitial result.1.2.1) result.2 := by
  apply onlinePointGateInitial_ready attempts limit (sharedOfflineFrame coin) input _ _ _ _ memory state
    ready.points (sharedOfflineFrame_pointRow coin input output sample) ready.coordinates ready.linkedLabels
    ready.represented (ready.curveReady attempts _) room result supported
  ring_nf at room ⊢
  omega

/-- An accepted actual link establishes all gate data and the exact shared state. -/
theorem onlineValidLinked_gateMemory [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support)
    (linkReady : OnlineLinkMemory
      (onlinePreparedMemory sampled.1 output (onlineSamplingCoin attempts
        (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled)) state coin input limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110)
    (linked : EncLinkResult)
    (linkedSupport : linked ∈ (encLinkSamples attempts
      (onlinePreparedMemory sampled.1 output (onlineSamplingCoin attempts
        (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled))
      state.family coin.2.2 []).support)
    (accepted : linked.1.2.2 = 7466) :
    let sample := onlineSamplingCoin attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    OnlineLinkedGateMemory coin input output sample linked.1.1 {state with family := linked.2} (limit + 508) := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin attempts base sampled
  let prepared := onlinePreparedMemory sampled.1 output sample
  have pointer : base.registers 10 = BitVec.ofNat 256 onlineSampleBase := by
    simp [base, onlineSampleInitial, onlineSampleSetup, executeLinear, LinearInstruction.execute]
  have data : OnlineLinkMemory prepared state coin input limit := linkReady
  have member : linked ∈ (encLinkSamples attempts prepared state.family coin.2.2 []).support := linkedSupport
  have notFailed : linked.1.2.2 ≠ 7467 := by rw [accepted]; decide
  have frame (cell : Nat) (lower : 256 ≤ cell) (upper : cell < onlineLinkedBase) :=
    encLinkSamples_beforeOutput attempts limit onlineLinkedBase cell prepared state.family coin.2.2 []
      data.represented.family data.represented.capacity data.operand data.outputPointer (by decide) (by decide)
      data.represented.counts.1 data.represented.counts.2.1 room hashRoom data.wire lower upper linked member
  have coordinates : prepared.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      prepared.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val :=
    onlinePreparedMemory_coordinates attempts base sampled.1 sampled.2 pointer supported input output sample
      (onlineCurveMemory_coordinates memory input (some output) [])
  have source := encLinkSamples_sharedMemory attempts prepared state coin.2.2 onlineLinkedBase limit []
    data.represented data.operand data.outputPointer (by decide) (by decide) room hashRoom data.wire linked member notFailed
  have words := encLinkSamples_memory attempts prepared state.family coin.2.2 onlineOriginalBase onlineLinkedBase limit []
    (encLinkMacLabels (coin.2.1.encodeAffine input)) (BitInput.ofAffine input).xBits (BitInput.ofAffine input).yBits
    data.represented.family data.represented.capacity data.operand data.inputPointer data.inputX data.inputY data.outputPointer
    (by decide) (by decide) (by decide) (by decide) data.labels (by
      intro first firstBound second secondBound
      have adjacent : onlineOriginalBase + 508 = onlineLinkedBase := by decide
      omega) data.represented.counts.1 data.represented.counts.2.1 room hashRoom data.wire linked member notFailed
  refine ⟨source.1, ?_, ?_, ?_, ?_, ?_, words.2.2.2.2⟩
  · have record := onlinePreparedMemory_curveRecord attempts memory sampled.1 sampled.2 coin input output sample stored supported
    apply record.congr _ _ _ prepared.ram linked.1.1.ram (BitVec.ofNat 256 privateBase) 834395
    intro offset bound
    rw [← BitVec.ofNat_add]
    apply frame
    · exact le_trans (by decide : 256 ≤ privateBase) (Nat.le_add_right _ _)
    · have fits := curveRecordOffset offset bound
      exact Nat.add_lt_add_left fits privateBase
  · exact encLinkSamples_pointMemory attempts limit prepared state coin.2.2 _ input _
      (onlineValidPrepared_pointMemory attempts memory input output coin stored sampled supported)
      data.represented data.operand data.outputPointer room hashRoom data.wire linked member
  · exact encLinkSamples_coordinates attempts limit prepared state coin.2.2 input coordinates data.represented
      data.operand data.outputPointer room hashRoom data.wire linked member
  · rw [frame (onlineInputBase + 2) (by decide) (by decide)]
    have kept := onlinePreparedMemory_outsidePoints attempts base sampled.1 sampled.2 pointer supported
      output sample 838210 (Or.inr (by decide)) (by decide)
    have address : BitVec.ofNat 256 privateBase + BitVec.ofNat 256 838210 =
        BitVec.ofNat 256 (onlineInputBase + 2) := by
      rw [← BitVec.ofNat_add]
      rfl
    rw [address] at kept
    change prepared.ram (BitVec.ofNat 256 (onlineInputBase + 2)) =
      (onlineCurveMemory memory input (some output) []).ram (BitVec.ofNat 256 (onlineInputBase + 2)) at kept
    rw [kept, onlineCurveMemory_tag]
    exact onlineOutputWords_present output
  · intro index inside
    have bound : index < 508 := by simpa [encLinkMacWords, coordinateBitCount] using inside
    simp only [Nat.zero_add]
    rw [← BitVec.ofNat_add, frame (onlineOriginalBase + index)]
    · simpa only [Nat.zero_add, BitVec.ofNat_add] using data.originalWords index inside
    · exact le_trans (by decide : 256 ≤ onlineOriginalBase) (Nat.le_add_right _ _)
    · exact lt_of_lt_of_le (Nat.add_lt_add_left bound onlineOriginalBase) (by decide)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
