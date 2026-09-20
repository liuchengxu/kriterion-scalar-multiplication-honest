import Proof.Privacy.Simulator.Arithmetic.RetargetPointSource
import Proof.Privacy.Simulator.Arithmetic.RetargetPointFrame
import Proof.Privacy.Simulator.Arithmetic.PublicLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
attribute [local irreducible] retargetAt

/-- Distinct bounded offsets select distinct words from one base pointer. -/
theorem privateOffset_ne (pointer : Word) (first second : Nat)
    (firstFits : first < 2 ^ 256) (secondFits : second < 2 ^ 256) (different : first ≠ second) :
    pointer + BitVec.ofNat 256 first ≠ pointer + BitVec.ofNat 256 second := by
  intro same
  have words := (BitVec.add_right_inj pointer).mp same
  have values := congrArg BitVec.toNat words
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt secondFits] at values
  exact different values

/-- A bounded offset also differs from a bounded base-plus-offset cell. -/
theorem privateOffset_add_ne (pointer : Word) (first second offset : Nat)
    (firstFits : first < 2 ^ 256) (secondFits : second + offset < 2 ^ 256)
    (different : first ≠ second + offset) :
    pointer + BitVec.ofNat 256 first ≠ pointer + BitVec.ofNat 256 second + BitVec.ofNat 256 offset := by
  simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using privateOffset_ne pointer first (second + offset)
    firstFits secondFits different

/-- One write preserves every disjoint source word. -/
theorem wordsAt_update (ram : Word → Word) (pointer : Word) (start : Nat) (words : List Word)
    (address value : Word) (stored : WordsAt ram pointer start words)
    (separate : ∀ index, index < words.length → pointer + BitVec.ofNat 256 (start + index) ≠ address) :
    WordsAt (Function.update ram address value) pointer start words := by
  intro index inside
  rw [Function.update_of_ne (separate index inside)]
  exact stored index inside

/-- Every selected request retains the four input factors. -/
theorem retargetAt_factors (kind : RetargetKind) (source target : Nat) (memory : Memory) (input : AffineInput)
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val) :
    ∀ factor, (executeLinear (retargetAt kind source 14 target) memory).registers (polynomialFactorRegister factor) =
      BitVec.ofNat 256 (polynomialInput input factor).val := by
  intro factor
  have bounds : 5 ≤ (polynomialFactorRegister factor).val ∧
      polynomialFactorRegister factor ≠ 10 ∧ polynomialFactorRegister factor ≠ 13 := by
    fin_cases factor <;> decide
  rw [(retargetAt_preserves kind source 14 target memory (by decide) (by decide)).2 _ bounds.1 bounds.2.1 bounds.2.2]
  exact encoded factor

/-- One complete row writes the three typed low targets in source order. -/
theorem retargetPointRow_ram (row : Fin FieldMacToECMac.outputMacCount) (sample : RowPublicSample) (input : AffineInput)
    (memory : Memory) (target : Fin 3 → BaseField)
    (stored : WordsAt memory.ram (memory.registers 11) (1017 + 9158 * row.val) (rowSchedule.words sample))
    (encoded : ∀ factor, memory.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (polynomialInput input factor).val)
    (requested : ∀ coordinate : Fin 3, memory.ram (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + coordinate.val)) =
      BitVec.ofNat 256 (target coordinate).val)
    (separate : ∀ coordinate : Fin 3, OutsidePointRow (memory.registers 11) row
      (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + coordinate.val))) :
    (executeLinear (retargetPointRow row) memory).ram =
      Function.update
        (Function.update
          (Function.update memory.ram (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 6105) + 762)
            (BitVec.ofNat 256 ((sample.x.request.retarget input (target 0)).x9Targets 0).val))
          (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val + 3815) + 508)
          (BitVec.ofNat 256 ((sample.y.request.retarget input (target 1)).x9Targets 0).val))
        (memory.registers 11 + BitVec.ofNat 256 (1017 + 9158 * row.val) + 1016)
        (BitVec.ofNat 256 ((sample.z.request.retarget input (target 2)).x9Targets 0).val) := by
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  let first := executeLinear (retargetAt .x (1017 + 9158 * row.val + 6105) 14 (3 * row.val)) memory
  let second := executeLinear (retargetAt .y (1017 + 9158 * row.val + 3815) 14 (3 * row.val + 1)) first
  have save (kind : RetargetKind) (source target : Nat) (base : Memory) (register : Register)
      (lower : 5 ≤ register.val) (notTen : register ≠ 10) (notThirteen : register ≠ 13) :=
    (retargetAt_preserves kind source 14 target base (by decide) (by decide)).2 register lower notTen notThirteen
  have firstSource : first.registers 11 = memory.registers 11 := save .x _ _ _ 11 (by decide) (by decide) (by decide)
  have firstTarget : first.registers 14 = memory.registers 14 := save .x _ _ _ 14 (by decide) (by decide) (by decide)
  have firstRam := xRetargetAt_ram sample.x input memory (target 0) _ _ (row_x_words sample _ _ _ stored) encoded
    (by simpa only [Fin.val_zero, Nat.add_zero] using requested 0)
  have remaining {start : Nat} {words : List Word} (source : WordsAt memory.ram (memory.registers 11) start words)
      (endBound : start + words.length ≤ 1017 + 9158 * row.val + 6105) :
      WordsAt first.ram (first.registers 11) start words := by
    rw [firstSource, firstRam]
    apply wordsAt_update _ _ _ _ _ _ source
    intro index inside
    apply privateOffset_add_ne _ (start + index) (1017 + 9158 * row.val + 6105) 762 <;> have r := row.isLt <;> omega
  have yWords := remaining (row_y_words sample _ _ _ stored) (by rw [(gateDataSchedule 4 3).wordsLength]; change _ + 2290 ≤ _; omega)
  have sep1 := separate 1
  change OutsidePointRow (memory.registers 11) row (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + 1)) at sep1
  have sep2 := separate 2
  change OutsidePointRow (memory.registers 11) row (memory.registers 14 + BitVec.ofNat 256 (3 * row.val + 2)) at sep2
  have yRequested : first.ram (first.registers 14 + BitVec.ofNat 256 (3 * row.val + 1)) = BitVec.ofNat 256 (target 1).val := by
    rw [firstTarget, firstRam, Function.update_of_ne sep1.1]
    exact requested 1
  have secondRam := yRetargetAt_ram sample.y input first (target 1) _ _ yWords
    (retargetAt_factors .x _ _ memory input encoded) yRequested
  have secondSource : second.registers 11 = memory.registers 11 :=
    (save .y _ _ _ 11 (by decide) (by decide) (by decide)).trans firstSource
  have secondTarget : second.registers 14 = memory.registers 14 :=
    (save .y _ _ _ 14 (by decide) (by decide) (by decide)).trans firstTarget
  have zWords : WordsAt second.ram (second.registers 11) (1017 + 9158 * row.val)
      ((gateDataSchedule 5 5).words (sample.z.coefficients, sample.z.tables, sample.z.quotients, sample.z.targets)) := by
    rw [secondSource, secondRam, firstSource]
    apply wordsAt_update
    · rw [← firstSource]
      exact remaining (row_z_words sample _ _ _ stored) (by rw [(gateDataSchedule 5 5).wordsLength]; change _ + 3815 ≤ _; omega)
    · intro index inside
      rw [(gateDataSchedule 5 5).wordsLength] at inside
      change index < 3815 at inside
      apply privateOffset_add_ne _ (1017 + 9158 * row.val + index) (1017 + 9158 * row.val + 3815) 508 <;> have r := row.isLt <;> omega
  have zRequested : second.ram (second.registers 14 + BitVec.ofNat 256 (3 * row.val + 2)) = BitVec.ofNat 256 (target 2).val := by
    rw [secondTarget, secondRam, firstSource, Function.update_of_ne sep2.2.1,
      firstRam, Function.update_of_ne sep2.1]
    exact requested 2
  have last := zRetargetAt_ram sample.z input second (target 2) _ _ zWords
    (retargetAt_factors .y _ _ first input (retargetAt_factors .x _ _ memory input encoded)) zRequested
  simp only [retargetPointRow, executeLinear_append]
  change (executeLinear (retargetAt .z (1017 + 9158 * row.val) 14 (3 * row.val + 2)) second).ram = _
  rw [last, secondRam, secondSource, firstRam, firstSource]

end Kriterion.ArgoMAC.ArithmeticSimulator
