import Proof.Privacy.Simulator.Arithmetic.RetargetPointRowSource
import Proof.Privacy.Simulator.Arithmetic.GateQuotientLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The curve descriptors read the exact retargeted target and unchanged auxiliary words. -/
theorem curveRetargeted_data (sample : CurvePublicSample) (input : AffineInput) (target : BaseField)
    (pointer : Word) (ram : Word → Word) (gate : Fin 5) (bit : Fin 254)
    (stored : WordsAt ram pointer 834395 ((gateDataSchedule 3 5).words
      (sample.coefficients, sample.tables, sample.quotients, sample.targets))) :
    let final := Function.update ram (pointer + 834903)
      (BitVec.ofNat 256 ((sample.request.retarget input target).x7Targets 0).val)
    final (pointer + BitVec.ofNat 256 (834395 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (if gate = 2 ∧ bit = 0 then ((sample.request.retarget input target).x7Targets 0).val
        else (sample.targets gate bit).val) ∧
    final (pointer + BitVec.ofNat 256 (834395 + 1270 + 254 * gate.val + bit.val)) =
      BitVec.ofNat 256 (sample.quotients gate bit).val ∧
    final (pointer + BitVec.ofNat 256 (834395 + 2540 + 254 * gate.val + bit.val)) =
      ((sample.tables gate).get bit).trueRow := by
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  have targetWord := gateData_target 3 5 _ ram pointer 834395 gate bit stored
  have quotientWord := gateData_quotient 3 5 _ ram pointer 834395 gate bit stored
  have tableWord := gateData_table 3 5 _ ram pointer 834395 gate bit stored
  simp only [coordinateBitCount, Nat.reduceMul] at targetWord quotientWord tableWord
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · by_cases selected : gate = 2 ∧ bit = 0
    · rcases selected with ⟨rfl, rfl⟩
      simp only [show (2 : Fin 5).val = 2 from rfl, show (0 : Fin 254).val = 0 from rfl, ↓reduceIte, Fin.val_ofNat, Nat.reduceMod, and_self, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Function.update_self]
    · rw [if_neg selected, Function.update_of_ne]
      · exact targetWord
      · apply privateOffset_ne pointer (834395 + 254 * gate.val + bit.val) 834903
        · omega
        · decide
        · intro same
          have positions : gate.val = 2 ∧ bit.val = 0 := by omega
          exact selected ⟨Fin.ext positions.1, Fin.ext positions.2⟩
  · rw [Function.update_of_ne]
    · exact quotientWord
    · apply privateOffset_ne pointer (834395 + 1270 + 254 * gate.val + bit.val) 834903 <;> omega
  · rw [Function.update_of_ne]
    · exact tableWord
    · apply privateOffset_ne pointer (834395 + 2540 + 254 * gate.val + bit.val) 834903 <;> omega

/-- The bit retarget operation changes only bit zero. -/
theorem retargetBits_value {count : Nat} (values : Fin (count + 1) → BaseField) (target : BaseField)
    (bit : Fin (count + 1)) :
    retargetBits values target bit = if bit = 0 then retargetBits values target 0 else values bit := by
  refine Fin.cases ?_ (fun index => ?_) bit
  · simp
  · simp only [retargetBits, Fin.cases_succ, Fin.succ_ne_zero, ↓reduceIte]

end Kriterion.ArgoMAC.ArithmeticSimulator
