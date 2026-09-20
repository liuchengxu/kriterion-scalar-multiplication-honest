import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBuffers
import Proof.Privacy.Simulator.Arithmetic.RetargetCurveSource
import Proof.Privacy.Simulator.Arithmetic.RetargetCurveGateWords

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The original-label prefix retains every offline source word. -/
theorem onlineOriginalMemory_before [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (cell : Nat) (lower : cell < onlineInputBase) :
    (onlineOriginalMemory memory input output rest).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  let read := onlineReadMemory memory input output rest
  have setup := onlineOriginalSetup_state read
  rw [onlineOriginalMemory, selectedLabelStoreCode_outside]
  · rw [setup.1]
    exact onlineReadMemory_before memory input output rest cell lower
  · intro index
    rw [setup.2.2.2.2, ← BitVec.ofNat_add]
    intro same
    have bound := index.isLt
    have first : cell < 2 ^ 256 := lt_trans lower (by decide)
    have second : onlineOriginalBase + index.val < 2 ^ 256 := by
      have fixed : onlineOriginalBase + 508 < 2 ^ 256 := by decide
      omega
    have values := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second] at values
    have separate : onlineInputBase < onlineOriginalBase := by decide
    omega

/-- The original-label prefix retains the complete offline word array. -/
theorem onlineOriginalMemory_offline [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    WordsAt (onlineOriginalMemory memory input output rest).ram (BitVec.ofNat 256 privateBase) 0
      (offlineSchedule.words coin) := by
  intro index inside
  rw [← BitVec.ofNat_add, onlineOriginalMemory_before]
  · simpa only [BitVec.ofNat_add] using stored index inside
  · rw [offlineSchedule.wordsLength] at inside
    unfold onlineInputBase
    omega

/-- The original-label prefix installs the source and coordinate pointers. -/
theorem onlineOriginalMemory_pointers [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    (onlineOriginalMemory memory input output rest).registers 11 = BitVec.ofNat 256 privateBase ∧
    (onlineOriginalMemory memory input output rest).registers 12 = BitVec.ofNat 256 onlineInputBase ∧
    (onlineOriginalMemory memory input output rest).registers 14 = BitVec.ofNat 256 onlineOriginalBase := by
  have setup := onlineOriginalSetup_state (onlineReadMemory memory input output rest)
  exact ⟨(selectedLabelStoreCode_caller _ 11 (by decide)).trans setup.2.2.1,
    (selectedLabelStoreCode_caller _ 12 (by decide)).trans setup.2.2.2.1,
    (selectedLabelStoreCode_caller _ 14 (by decide)).trans setup.2.2.2.2⟩

/-- The reader stores both input coordinates at the fixed input pointer. -/
theorem onlineReadMemory_coordinates [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val := by
  rw [onlineReadMemory, (onlineInputMemory_values (onlineInputPrepared memory) input output rest).1]
  have pointer : (onlineInputPrepared memory).registers 10 = BitVec.ofNat 256 onlineInputBase := rfl
  have apart (a b : Word) (different : a ≠ b) :
      BitVec.ofNat 256 onlineInputBase + a ≠ BitVec.ofNat 256 onlineInputBase + b :=
    fun same => different (add_left_cancel same)
  simp only [onlineRecordRam, pointer]
  constructor
  · have z (b : Word) (different : (0 : Word) ≠ b) :
        BitVec.ofNat 256 onlineInputBase ≠ BitVec.ofNat 256 onlineInputBase + b := by
        simpa using apart 0 b different
    rw [Function.update_of_ne (z 4 (by decide)), Function.update_of_ne (z 3 (by decide)),
      Function.update_of_ne (z 2 (by decide)), Function.update_of_ne (z 1 (by decide)), Function.update_self]
  · rw [Function.update_of_ne (apart 1 4 (by decide)), Function.update_of_ne (apart 1 3 (by decide)),
      Function.update_of_ne (apart 1 2 (by decide)), Function.update_self]

/-- The original-label store preserves the complete parsed input record. -/
theorem onlineOriginalMemory_input [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (offset : Fin 5) :
    (onlineOriginalMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + offset.val)) =
      (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + offset.val)) := by
  have setup := onlineOriginalSetup_state (onlineReadMemory memory input output rest)
  rw [onlineOriginalMemory, selectedLabelStoreCode_outside]
  · exact congrFun setup.1 _
  · intro index
    rw [setup.2.2.2.2]
    exact onlineInput_labelSeparate offset index

/-- The original-label prefix provides both coordinates for curve retargeting. -/
theorem onlineOriginalMemory_coordinates [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    let current := onlineOriginalMemory memory input output rest
    current.ram (current.registers 12) = BitVec.ofNat 256 input.x.val ∧
    current.ram (current.registers 12 + 1) = BitVec.ofNat 256 input.y.val := by
  dsimp only
  have values := onlineReadMemory_coordinates memory input output rest
  have x := onlineOriginalMemory_input memory input output rest 0
  have y := onlineOriginalMemory_input memory input output rest 1
  rw [(onlineOriginalMemory_pointers memory input output rest).2.1]
  simpa only [Fin.val_zero, Nat.add_zero, Fin.val_one, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
    And.intro (x.trans values.1) (y.trans values.2)

/-- The curve prefix writes the exact source target and retains all other source words. -/
theorem onlineCurveMemory_ram [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    (onlineCurveMemory memory input output rest).ram =
      Function.update (onlineOriginalMemory memory input output rest).ram
        (BitVec.ofNat 256 privateBase + 834903)
        (BitVec.ofNat 256 ((coin.1.curve.request.retarget input coin.2.2).x7Targets 0).val) := by
  let original := onlineOriginalMemory memory input output rest
  have source := onlineOriginalMemory_offline memory input output rest coin stored
  have pointers := onlineOriginalMemory_pointers memory input output rest
  have curve := public_curve_words coin.1 original.ram (BitVec.ofNat 256 privateBase)
    (offline_public_words coin original.ram _ source)
  have pair := wordsAt_pair_right publicSchedule (inputKeySchedule.pair fieldSchedule) original.ram _ 0 coin source
  have field := wordsAt_pair_right inputKeySchedule fieldSchedule original.ram _ 0 coin.2 pair
  have target := wordsAt_field original.ram _ 0 coin.2.2 field
  apply Eq.trans (retargetCurveCode_ram coin.1.curve input original coin.2.2 ?_ ?_ ?_) ?_
  · rw [pointers.1]
    exact curve
  · exact onlineOriginalMemory_coordinates memory input output rest
  · rw [pointers.1]
    simpa using target
  · rw [pointers.1]

/-- Every reached curve descriptor has its exact three typed source words. -/
theorem onlineCurveMemory_gateWords [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (gate : Fin 5) (bit : Fin 254) :
    let final := onlineCurveMemory memory input output rest
    final.ram (BitVec.ofNat 256 privateBase + BitVec.ofNat 256 (834395 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 2 ∧ bit = 0 then ((coin.1.curve.request.retarget input coin.2.2).x7Targets 0).val
        else (coin.1.curve.targets gate bit).val) ∧
    final.ram (BitVec.ofNat 256 privateBase + BitVec.ofNat 256 (834395 + 1270 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (coin.1.curve.quotients gate bit).val ∧
    final.ram (BitVec.ofNat 256 privateBase + BitVec.ofNat 256 (834395 + 2540 + 254 * gate.val + bit.val)) =
      ((coin.1.curve.tables gate).get bit).trueRow := by
  dsimp only
  rw [onlineCurveMemory_ram memory input output rest coin stored]
  exact curveRetargeted_data coin.1.curve input coin.2.2 _ _ gate bit
    (public_curve_words coin.1 _ _ (offline_public_words coin _ _
      (onlineOriginalMemory_offline memory input output rest coin stored)))

end Kriterion.ArgoMAC.ArithmeticSimulator
