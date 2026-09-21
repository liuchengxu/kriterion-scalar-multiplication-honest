import Proof.Privacy.Simulator.Arithmetic.EncLinkOracleLaw
import Proof.Privacy.Simulator.Arithmetic.EncLinkLazyMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineActualReady
namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The private sampler retains the selected output point. -/
theorem lazyOnline_sampled_selected [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    selectedOutputPoint sampled.1.ram (BitVec.ofNat 256 onlineInputBase) = some output := by
  rw [onlineSamplingMemory_selectedOutput 256 _ sampled.1 sampled.2 (by rfl) supported]
  exact selectedOutputPoint_curve memory input output

/-- Each lazy link return reaches the gate phase with the output tag intact. -/
theorem lazyOnline_linked_ready [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (linked : (Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (member : linked ∈ (lazyEncLinkSamples (onlinePreparedMemory sampled.1 output
      (onlineSamplingCoin 256 (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled)) oracle).support) :
    linked.1.2.2 = 7466 ∧ linked.1.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin 256 base sampled
  let prepared := onlinePreparedMemory sampled.1 output sample
  have pointer : prepared.registers 14 = BitVec.ofNat 256 onlineLinkedBase :=
    (onlineLinkSetup_state _).2.2.2.1
  obtain ⟨complete, same⟩ := lazyEncLinkSamples_witness prepared oracle linked member
  rw [← same]
  refine ⟨eagerEncLinkSamples_terminal complete prepared onlineLinkedBase pointer (by decide) (by decide), ?_⟩
  rw [eagerEncLinkSamples_frame complete prepared onlineLinkedBase (onlineInputBase + 2) pointer
    (by decide) (by decide) (by decide) (by decide) (by intro offset inside; unfold onlineLinkedBase onlineInputBase; omega)]
  have kept := onlinePreparedMemory_outsidePoints 256 base sampled.1 sampled.2 (by rfl) supported
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

/-- The link receives only its typed private operands. -/
structure LazyOnlineLinkData (memory : Memory) (coin : OfflineCoin) (input : AffineInput) : Prop where
  operand : memory.registers 8 = hashKeyWord coin.2.2
  inputPointer : memory.registers 11 = BitVec.ofNat 256 onlineOriginalBase
  outputPointer : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase
  inputX : memory.registers 12 = (BitInput.ofAffine input).xBits.setWidth 256
  inputY : memory.registers 13 = (BitInput.ofAffine input).yBits.setWidth 256
  labels : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    (List.ofFn fun index => (encLinkMacLabels (coin.2.1.encodeAffine input) index).setWidth 256)
  originalWords : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256))

/-- Private preparation gives the link every typed operand. -/
theorem lazyOnline_linkData [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    let sample := onlineSamplingCoin 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    LazyOnlineLinkData (onlinePreparedMemory sampled.1 output sample) coin input := by
  let initial := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin 256 initial sampled
  let before := executeLinear retargetPointCode
    (executeLinear onlineRetargetSetup (onlineTargetMemory sampled.1 output sample))
  let prepared := onlinePreparedMemory sampled.1 output sample
  have link := onlineLinkSetup_state before
  have pointer : initial.registers 10 = BitVec.ofNat 256 onlineSampleBase := rfl
  have initialRam : initial.ram = (onlineCurveMemory memory input (some output) []).ram := rfl
  have coordinates := onlinePreparedMemory_coordinates 256 initial sampled.1 sampled.2 pointer supported
    input output sample (onlineCurveMemory_coordinates memory input (some output) [])
  have labels := onlinePreparedMemory_labels 256 initial sampled.1 sampled.2 pointer supported output sample
    (coin.2.1.encodeAffine input) (onlineCurveMemory_labels memory input (some output) [] coin stored)
  have after := wordsAt_pair_right publicSchedule (inputKeySchedule.pair fieldSchedule) memory.ram _ 0 coin stored
  have key := wordsAt_field memory.ram _ 0 coin.2.2
    (wordsAt_pair_right inputKeySchedule fieldSchedule memory.ram _ 0 coin.2 after)
  have bridge : prepared.ram (BitVec.ofNat 256 privateBase) = BitVec.ofNat 256 coin.2.2.val := by
    have frame := onlinePreparedMemory_outsidePoints 256 initial sampled.1 sampled.2 pointer supported output sample
      0 (Or.inl (by decide)) (by decide)
    simp only [show BitVec.ofNat 256 0 = (0 : Word) from rfl, add_zero] at frame
    rw [frame, initialRam, onlineCurveMemory_before memory input (some output) [] privateBase (by omega)]
    simpa using key
  have linkRam : prepared.ram = before.ram := link.1
  have operand : prepared.registers 8 = before.ram (BitVec.ofNat 256 privateBase) := link.2.2.2.2.2.2
  have inputX : prepared.registers 12 = before.ram (BitVec.ofNat 256 onlineInputBase) := link.2.2.2.2.1
  have inputY : prepared.registers 13 = before.ram (BitVec.ofNat 256 (onlineInputBase + 1)) := link.2.2.2.2.2.1
  refine ⟨?_, link.2.2.1, link.2.2.2.1, ?_, ?_, ?_, labels⟩
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

/-- The linked memory contains the private data for both gate loops. -/
structure LazyOnlineGateData [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (input : AffineInput) (output : Point)
    (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) (mac : InputMac) (memory : Memory) : Prop where
  curve : RetargetedGateMemory
    (coin.1.curve.coefficients, coin.1.curve.tables, coin.1.curve.quotients, coin.1.curve.targets)
    2 ((coin.1.curve.request.retarget input coin.2.2).x7Targets 0) memory.ram (BitVec.ofNat 256 privateBase) 834395
  points : PointGateMemory (fun row => coin.1.points.get row) input (onlineTargetField output sample)
    memory.ram (BitVec.ofNat 256 privateBase)
  coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val
  originalLabels : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
    ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256))
  linkedLabels : WordsAt memory.ram (BitVec.ofNat 256 onlineLinkedBase) 0
    ((encLinkMacWords mac).map (fun label => label.setWidth 256))
  keys : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words coin.2.1)
  empty : memory.bits 3 = []

attribute [local irreducible] onlineSamplingCoin onlineSamplingMemory onlinePreparedMemory eagerEncLinkSamples

/-- Every complete link execution retains all private gate data. -/
theorem eagerOnline_gateData [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support)
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    let sample := onlineSamplingCoin 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    LazyOnlineGateData coin input output sample
      (encLinkOutputMac (eagerEncLinkSamples oracle (onlinePreparedMemory sampled.1 output sample)).1 onlineLinkedBase)
      (eagerEncLinkSamples oracle (onlinePreparedMemory sampled.1 output sample)).1 := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin 256 base sampled
  let prepared := onlinePreparedMemory sampled.1 output sample
  let linked := (eagerEncLinkSamples oracle prepared).1
  have pointer : base.registers 10 = BitVec.ofNat 256 onlineSampleBase := rfl
  have data : LazyOnlineLinkData prepared coin input := lazyOnline_linkData memory input output coin stored sampled supported
  have frame (cell : Nat) (lower : 256 ≤ cell) (upper : cell < onlineLinkedBase) :
      linked.ram (BitVec.ofNat 256 cell) = prepared.ram (BitVec.ofNat 256 cell) :=
    eagerEncLinkSamples_frame oracle prepared onlineLinkedBase cell data.outputPointer (by decide) (by decide)
      lower (lt_trans upper (by decide)) (by intro offset inside equal; omega)
  have coordinates := onlinePreparedMemory_coordinates 256 base sampled.1 sampled.2 pointer supported
    input output sample (onlineCurveMemory_coordinates memory input (some output) [])
  have words := eagerEncLinkSamples_words oracle prepared onlineOriginalBase onlineLinkedBase
    (encLinkMacLabels (coin.2.1.encodeAffine input)) (BitInput.ofAffine input).xBits (BitInput.ofAffine input).yBits
    data.inputPointer data.inputX data.inputY data.outputPointer (by decide) (by decide) (by decide) (by decide)
    data.labels (by intro first firstBound second secondBound; unfold onlineOriginalBase onlineLinkedBase; omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have record := onlinePreparedMemory_curveRecord 256 memory sampled.1 sampled.2 coin input output sample stored supported
    apply record.congr _ _ _ prepared.ram linked.ram (BitVec.ofNat 256 privateBase) 834395
    intro offset bound
    rw [← BitVec.ofNat_add]
    exact frame _ (by unfold privateBase; omega) (by unfold onlineLinkedBase privateBase; omega)
  · apply (onlineValidPrepared_pointMemory 256 memory input output coin stored sampled supported).privateFrame
      (fun row => coin.1.points.get row) input (onlineTargetField output sample) prepared.ram linked.ram
    intro cell lower upper
    exact frame cell (le_trans (by decide) lower) (lt_trans upper (by decide))
  · constructor
    · exact (frame onlineInputBase (by decide) (by decide)).trans coordinates.1
    · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by rw [BitVec.ofNat_add]; rfl
      rw [address]
      exact (frame (onlineInputBase + 1) (by decide) (by decide)).trans (address ▸ coordinates.2)
  · intro index inside
    have bound : index < 508 := by simpa [encLinkMacWords, coordinateBitCount] using inside
    simp only [Nat.zero_add]
    rw [← BitVec.ofNat_add, frame (onlineOriginalBase + index) (by unfold onlineOriginalBase; omega)
      (by unfold onlineOriginalBase onlineLinkedBase; omega)]
    simpa only [Nat.zero_add, BitVec.ofNat_add] using data.originalWords index inside
  · apply encLinkOutputMac_wordsAt
    intro offset inside
    have value := words offset (by simpa using inside)
    simp only [Nat.zero_add, ← BitVec.ofNat_add, List.getElem_map, List.getElem_finRange] at value
    rw [value]
    simp
  · have keys := onlinePreparedMemory_keys 256 base sampled.1 sampled.2 pointer supported output sample coin.2.1
      (onlineCurveMemory_keys memory input (some output) [] coin stored)
    intro index inside
    have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
    rw [← BitVec.ofNat_add, frame (privateBase + (1 + index)) (by unfold privateBase; omega)
      (by unfold onlineLinkedBase privateBase; omega)]
    simpa only [BitVec.ofNat_add] using keys index inside
  · rw [eagerEncLinkSamples_bits_other oracle prepared 3 (by decide), onlinePreparedMemory_bits,
      onlineSamplingMemory_bits 256 base sampled.1 sampled.2 supported]
    change (onlineCurveMemory memory input (some output) []).bits 3 = []
    rw [onlineCurveMemory_bits]
    exact empty

/-- Private RAM equality preserves a bounded word array. -/
private theorem privateWords_frame (memory next : Memory)
    (same : ∀ cell, 32 ≤ cell → cell < 2 ^ 96 → next.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell))
    (base start : Nat) (words : List Word) (lower : 32 ≤ base) (upper : base + start + words.length ≤ 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 base) start words) :
    WordsAt next.ram (BitVec.ofNat 256 base) start words := by
  intro index inside
  rw [← BitVec.ofNat_add, same (base + (start + index)) (by omega) (by omega), BitVec.ofNat_add]
  exact stored index inside

/-- Gate execution preserves all typed private inputs. -/
theorem LazyOnlineGateData.frame [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory next : Memory}
    (data : LazyOnlineGateData coin input output sample mac memory)
    (same : ∀ cell, 32 ≤ cell → cell < 2 ^ 96 → next.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell))
    (bits : next.bits 3 = memory.bits 3) : LazyOnlineGateData coin input output sample mac next := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, bits.trans data.empty⟩
  · apply data.curve.congr _ _ _ memory.ram next.ram (BitVec.ofNat 256 privateBase) 834395
    intro offset bound
    rw [← BitVec.ofNat_add]
    exact same _ (by unfold privateBase; omega) (by unfold privateBase; omega)
  · apply data.points.privateFrame _ _ _ memory.ram next.ram
    intro cell lower upper
    exact same cell (le_trans (by decide) lower) (lt_trans upper (by decide))
  · constructor
    · exact (same onlineInputBase (by decide) (by decide)).trans data.coordinates.1
    · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by rw [BitVec.ofNat_add]; rfl
      rw [address]
      exact (same (onlineInputBase + 1) (by decide) (by decide)).trans (address ▸ data.coordinates.2)
  · exact privateWords_frame memory next same onlineOriginalBase 0 _ (by decide)
      (by simp only [List.length_map, encLinkMacWords, List.length_append, Vector.length_toList]; decide) data.originalLabels
  · exact privateWords_frame memory next same onlineLinkedBase 0 _ (by decide)
      (by simp only [List.length_map, encLinkMacWords, List.length_append, Vector.length_toList]; decide) data.linkedLabels
  · exact privateWords_frame memory next same privateBase 1 _ (by decide)
      (by rw [inputKeySchedule.wordsLength]; decide) data.keys

/-- The private curve records determine each strict command. -/
theorem LazyOnlineGateData.curvePlan [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory) (index : Fin 1270) :
    GateTypedData (onlineGateInitial memory) curveGatePlan[index.val]
      (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input) input
        ((sharedOfflineFrame coin).labels input).inputMac index)
      (coin.1.curve.quotients ⟨index.val / 254, by have := index.isLt; omega⟩
        ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩) := by
  have setup := onlineOriginalSetup_state memory
  have data (gate : Fin 5) (bit : Fin 254) :
      GateTypedData (onlineGateInitial memory) (curveGateCode gate bit)
        ((coin.1.curve.request.retarget input coin.2.2).actualDirective input (coin.2.1.encodeAffine input) gate bit)
        (coin.1.curve.quotients gate bit) := by
    apply curveGateCode_typed coin.1.curve input coin.2.2 (coin.2.1.encodeAffine input) _ gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.2.1]; exact ready.coordinates
    · rw [onlineGateInitial, setup.1, setup.2.2.2.2]; exact ready.originalLabels
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact ready.curve.target gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact ready.curve.quotient gate bit
    · rw [onlineGateInitial, setup.1, setup.2.2.1]; exact ready.curve.table gate bit
  simpa only [curveGatePlan, Vector.getElem_ofFn, curveDirectiveAt, onlineGateInitial,
    sharedOfflineFrame_curve, sharedOfflineFrame_inputMac] using
    data ⟨index.val / 254, by have := index.isLt; omega⟩ ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩

/-- The private point records determine each strict command. -/
theorem LazyOnlineGateData.pointPlan [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory) (index : Fin 277368) :
    ∃ quotient, GateTypedData (onlinePointGateInitial memory) pointGatePlan[index.val]
      (pointDirectiveAt ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
        input mac index) quotient := by
  have setup := onlinePointSetup_state (onlineTagMemory memory)
  apply PointGateMemory.plan (fun row => coin.1.points.get row) input (onlineTargetField output sample)
    (onlinePointGateInitial memory) mac _
  · rw [onlinePointGateInitial, setup.1, setup.2.2.1]
    exact ready.points
  · exact sharedOfflineFrame_pointRow coin input output sample
  · rw [onlinePointGateInitial, setup.1, setup.2.2.2.1]
    exact ready.coordinates
  · rw [onlinePointGateInitial, setup.1, setup.2.2.2.2]
    exact ready.linkedLabels

/-- The eager linked MAC equals the typed source's EncPRF output. -/
theorem eagerOnline_mac [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support)
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    let sample := onlineSamplingCoin 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    encLinkOutputMac (eagerEncLinkSamples oracle (onlinePreparedMemory sampled.1 output sample)).1 onlineLinkedBase =
      EncPRF.transformMac oracle.2.1 (EncPRF.whiteningKeys oracle.2.2 coin.2.2) (BitInput.ofAffine input)
        (coin.2.1.encodeAffine input) := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  let sample := onlineSamplingCoin 256 base sampled
  let prepared := onlinePreparedMemory sampled.1 output sample
  have data : LazyOnlineLinkData prepared coin input := lazyOnline_linkData memory input output coin stored sampled supported
  have mac := eagerEncLinkSamples_mac oracle prepared onlineOriginalBase onlineLinkedBase (BitInput.ofAffine input)
    (coin.2.1.encodeAffine input) data.inputPointer data.inputX data.inputY data.outputPointer
    (by decide) (by decide) (by decide) (by decide) data.labels
    (by intro first firstBound second secondBound; unfold onlineOriginalBase onlineLinkedBase; omega)
  have key : ((prepared.registers 8).toNat : BaseField) = coin.2.2 := by
    rw [data.operand, hashKeyWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans coin.2.2.val_lt (by decide : baseFieldModulus < 2 ^ 256))]
    exact ZMod.natCast_zmod_val _
  simpa only [key] using mac
end
end Kriterion.ArgoMAC.ArithmeticSimulator
