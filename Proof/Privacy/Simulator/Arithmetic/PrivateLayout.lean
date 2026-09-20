import Proof.Privacy.Simulator.Arithmetic.WordsAt

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling

/-- A count cast does not change the stored words. -/
theorem privateSchedule_cast_words {A : Type} {first second : Nat} {source : Code A first}
    (schedule : PrivateSchedule source) (same : first = second) (value : A) :
    (schedule.cast same).words value = schedule.words value := by
  cases same
  rfl

/-- The first source in a pair follows the second source's words. -/
theorem wordsAt_pair_left {A B : Type} {first second : Nat} {left : Code A first} {right : Code B second}
    (leftSchedule : PrivateSchedule left) (rightSchedule : PrivateSchedule right)
    (ram : Word → Word) (pointer : Word) (start : Nat) (value : A × B)
    (stored : WordsAt ram pointer start ((leftSchedule.pair rightSchedule).words value)) :
    WordsAt ram pointer (start + second) (leftSchedule.words value.1) := by
  have selected := wordsAt_append_right stored
  simpa only [rightSchedule.wordsLength] using selected

/-- The second source in a pair starts at the pair's first address. -/
theorem wordsAt_pair_right {A B : Type} {first second : Nat} {left : Code A first} {right : Code B second}
    (leftSchedule : PrivateSchedule left) (rightSchedule : PrivateSchedule right)
    (ram : Word → Word) (pointer : Word) (start : Nat) (value : A × B)
    (stored : WordsAt ram pointer start ((leftSchedule.pair rightSchedule).words value)) :
    WordsAt ram pointer start (rightSchedule.words value.2) := wordsAt_append_left stored

/-- Each source vector places one record at its fixed offset. -/
theorem wordsAt_scheduleVector {A : Type} {draws : Nat} {source : Code A draws}
    (schedule : PrivateSchedule source) (count : Nat) (value : Vector A count)
    (ram : Word → Word) (pointer : Word) (start : Nat) (index : Fin count)
    (stored : WordsAt ram pointer start ((schedule.vector count).words value)) :
    WordsAt ram pointer (start + draws * index.val) (schedule.words (value.get index)) :=
  wordsAt_vector schedule.words draws schedule.wordsLength value ram pointer start index stored

/-- A field source stores its canonical 256-bit representation. -/
theorem wordsAt_field (ram : Word → Word) (pointer : Word) (start : Nat) (value : BaseField)
    (stored : WordsAt ram pointer start (fieldSchedule.words value)) :
    ram (pointer + BitVec.ofNat 256 start) = BitVec.ofNat 256 value.val := by
  simpa only [Nat.add_zero, fieldSchedule, PrivateSchedule.primitive, List.getElem_cons_zero] using stored 0 (by rw [fieldSchedule.wordsLength]; decide)

/-- A ciphertext source stores its complete random row. -/
theorem wordsAt_table (ram : Word → Word) (pointer : Word) (start : Nat) (value : BitAdaptor.Table)
    (stored : WordsAt ram pointer start (tableSchedule.words value)) :
    ram (pointer + BitVec.ofNat 256 start) = value.trueRow := by
  have selected := stored 0 (by rw [tableSchedule.wordsLength]; decide)
  simpa only [Nat.add_zero, tableSchedule, PrivateSchedule.equiv, bitsSchedule,
    PrivateSchedule.primitive, List.getElem_cons_zero, tableEquiv, Equiv.coe_fn_symm_mk,
    BitVec.setWidth_eq] using selected

end Kriterion.ArgoMAC.ArithmeticSimulator
