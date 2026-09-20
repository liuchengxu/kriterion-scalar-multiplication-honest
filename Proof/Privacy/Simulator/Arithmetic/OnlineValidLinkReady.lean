import Proof.Privacy.Simulator.Arithmetic.OnlinePreparedLabels
import Proof.Privacy.Simulator.Arithmetic.OnlinePreparedSource
import Proof.Privacy.Simulator.Arithmetic.OnlineJointFrame
import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBits
import Proof.Privacy.Simulator.Arithmetic.OnlineAbortBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine

/-- The actual link entry stores the exact source and all typed operands. -/
structure OnlineLinkMemory (memory : Memory) (state : SharedOracleSource) (coin : OfflineCoin)
    (input : AffineInput) (limit : Nat) : Prop where
  represented : SharedSourceMemory memory state limit
  operand : memory.registers 8 = hashKeyWord coin.2.2
  inputPointer : memory.registers 11 = BitVec.ofNat 256 onlineOriginalBase
  outputPointer : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase
  inputX : memory.registers 12 = (BitInput.ofAffine input).xBits.setWidth 256
  inputY : memory.registers 13 = (BitInput.ofAffine input).yBits.setWidth 256
  labels : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    (List.ofFn fun index => (encLinkMacLabels (coin.2.1.encodeAffine input) index).setWidth 256)
  originalWords : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256))
  wire : memory.bits 0 = []

/-- The flat MAC array has the exact index function used by the link source. -/
theorem encLinkMacWords_labels (mac : InputMac) :
    (encLinkMacWords mac).map (fun label => label.setWidth 256) =
      List.ofFn (fun index => (encLinkMacLabels mac index).setWidth 256) := by
  rw [encLinkMacWords_selected]
  simp only [Lamport.selectedLabels, Vector.toList_ofFn, List.map_ofFn]
  apply congrArg List.ofFn
  funext index
  by_cases low : index.val < 254 <;> simp [encLinkMacLabels, encLinkIndexAt, low, Vector.get]

/-- A canonical field word equals the widened coordinate-bit word. -/
theorem coordinateBits_widen (value : BaseField) :
    BitVec.ofNat 256 value.val = (coordinateBits value).setWidth 256 := by
  have bound : value.val < 2 ^ 254 := lt_trans value.val_lt (by decide : baseFieldModulus < 2 ^ 254)
  apply BitVec.eq_of_toNat_eq
  simp [coordinateBits, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    Nat.mod_eq_of_lt (lt_trans bound (by decide : 2 ^ 254 < 2 ^ 256))]

/-- The actual valid prefix supplies every source and operand premise for the link. -/
theorem onlineValidLink_ready [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (coin : OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    let sample := onlineSamplingCoin attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    OnlineLinkMemory (onlinePreparedMemory sampled.1 output sample) state coin input limit := by
  let initial := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin attempts initial sampled
  let before := executeLinear retargetPointCode
    (executeLinear onlineRetargetSetup (onlineTargetMemory sampled.1 output sample))
  let prepared := onlinePreparedMemory sampled.1 output sample
  have link := onlineLinkSetup_state before
  have pointer : initial.registers 10 = BitVec.ofNat 256 onlineSampleBase := rfl
  have initialRam : initial.ram = (onlineCurveMemory memory input (some output) []).ram := rfl
  have initialCoordinates := onlineCurveMemory_coordinates memory input (some output) []
  have coordinates := onlinePreparedMemory_coordinates attempts initial sampled.1 sampled.2 pointer supported
    input output sample initialCoordinates
  have labels := onlinePreparedMemory_labels attempts initial sampled.1 sampled.2 pointer supported output sample
    (coin.2.1.encodeAffine input) (onlineCurveMemory_labels memory input (some output) [] coin stored)
  have after := wordsAt_pair_right publicSchedule (inputKeySchedule.pair fieldSchedule) memory.ram _ 0 coin stored
  have key := wordsAt_field memory.ram _ 0 coin.2.2
    (wordsAt_pair_right inputKeySchedule fieldSchedule memory.ram _ 0 coin.2 after)
  have bridge : prepared.ram (BitVec.ofNat 256 privateBase) = BitVec.ofNat 256 coin.2.2.val := by
    have frame := onlinePreparedMemory_outsidePoints attempts initial sampled.1 sampled.2 pointer supported output sample
      0 (Or.inl (by decide)) (by decide)
    simp only [show BitVec.ofNat 256 0 = (0 : Word) from rfl, add_zero] at frame
    rw [frame, initialRam, onlineCurveMemory_before memory input (some output) [] privateBase (by omega)]
    simpa using key
  have linkRam : prepared.ram = before.ram := link.1
  have operand : prepared.registers 8 = before.ram (BitVec.ofNat 256 privateBase) := link.2.2.2.2.2.2
  have inputX : prepared.registers 12 = before.ram (BitVec.ofNat 256 onlineInputBase) := link.2.2.2.2.1
  have inputY : prepared.registers 13 = before.ram (BitVec.ofNat 256 (onlineInputBase + 1)) := link.2.2.2.2.2.1
  refine ⟨onlineValidPrepared_shared attempts limit memory input output state represented room sampled supported,
    ?_, link.2.2.1, link.2.2.2.1, ?_, ?_, ?_, labels, ?_⟩
  · change prepared.registers 8 = hashKeyWord coin.2.2
    rw [operand, ← linkRam]
    exact bridge
  · change prepared.registers 12 = _
    rw [inputX, ← linkRam]
    exact coordinates.1.trans (coordinateBits_widen input.x)
  · change prepared.registers 13 = _
    rw [inputY, ← linkRam]
    exact coordinates.2.trans (coordinateBits_widen input.y)
  · rw [← encLinkMacWords_labels]
    exact labels
  · change prepared.bits 0 = []
    rw [onlinePreparedMemory_bits, onlineSamplingMemory_bits attempts initial sampled.1 sampled.2 supported]
    change (onlineCurveMemory memory input (some output) []).bits 0 = []
    rw [onlineCurveMemory_bits, Function.update_self]

end Kriterion.ArgoMAC.ArithmeticSimulator
