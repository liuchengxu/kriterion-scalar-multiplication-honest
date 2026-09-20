import Proof.Privacy.Simulator.Arithmetic.PrivateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

/-- The offline input key follows the one-word bridge key. -/
theorem offline_inputKey_words (coin : OfflineCoin) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 0 (offlineSchedule.words coin)) :
    WordsAt ram pointer 1 (inputKeySchedule.words coin.2.1) := by
  have after := wordsAt_pair_right publicSchedule (inputKeySchedule.pair fieldSchedule) ram pointer 0 coin stored
  exact wordsAt_pair_left inputKeySchedule fieldSchedule ram pointer 0 coin.2 after

/-- The x-coordinate keys follow the 508 y-coordinate key words. -/
theorem inputKey_x_words (key : InputMacKey) (ram : Word → Word) (pointer : Word) (start : Nat)
    (stored : WordsAt ram pointer start (inputKeySchedule.words key)) :
    WordsAt ram pointer (start + 508) ((keySchedule.vector 254).words key.x) := by
  exact wordsAt_pair_left (keySchedule.vector 254) (keySchedule.vector 254) ram pointer start (key.x, key.y) stored

/-- The y-coordinate keys occupy the first input-key words. -/
theorem inputKey_y_words (key : InputMacKey) (ram : Word → Word) (pointer : Word) (start : Nat)
    (stored : WordsAt ram pointer start (inputKeySchedule.words key)) :
    WordsAt ram pointer start ((keySchedule.vector 254).words key.y) := by
  exact wordsAt_pair_right (keySchedule.vector 254) (keySchedule.vector 254) ram pointer start (key.x, key.y) stored

/-- One sampled block occupies one zero-extended machine word. -/
theorem wordsAt_block (ram : Word → Word) (pointer : Word) (start : Nat) (value : Cryptography.Block)
    (stored : WordsAt ram pointer start ((bitsSchedule 128 (by decide)).words value)) :
    ram (pointer + BitVec.ofNat 256 start) = value.setWidth 256 := by
  simpa only [Nat.add_zero, bitsSchedule, PrivateSchedule.primitive, List.getElem_cons_zero] using
    stored 0 (by rw [(bitsSchedule 128 (by decide)).wordsLength]; decide)

/-- Each key record stores its true label before its false label. -/
theorem wordsAt_key (ram : Word → Word) (pointer : Word) (start : Nat) (key : BitAdaptor.Key)
    (stored : WordsAt ram pointer start (keySchedule.words key)) :
    ram (pointer + BitVec.ofNat 256 start) = key.trueLabel.setWidth 256 ∧
    ram (pointer + BitVec.ofNat 256 (start + 1)) = key.falseLabel.setWidth 256 := by
  constructor
  · exact wordsAt_block ram pointer start key.trueLabel
      (wordsAt_pair_right (bitsSchedule 128 (by decide)) (bitsSchedule 128 (by decide))
        ram pointer start (key.falseLabel, key.trueLabel) stored)
  · exact wordsAt_block ram pointer (start + 1) key.falseLabel
      (wordsAt_pair_left (bitsSchedule 128 (by decide)) (bitsSchedule 128 (by decide))
        ram pointer start (key.falseLabel, key.trueLabel) stored)

/-- Every x-coordinate label pair has its exact offline address. -/
theorem offline_x_key (coin : OfflineCoin) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 0 (offlineSchedule.words coin)) (i : Fin 254) :
    ram (pointer + BitVec.ofNat 256 (509 + 2 * i.val)) = (coin.2.1.x.get i).trueLabel.setWidth 256 ∧
    ram (pointer + BitVec.ofNat 256 (510 + 2 * i.val)) = (coin.2.1.x.get i).falseLabel.setWidth 256 := by
  have keys := inputKey_x_words coin.2.1 ram pointer 1 (offline_inputKey_words coin ram pointer stored)
  have selected := wordsAt_scheduleVector keySchedule 254 coin.2.1.x ram pointer 509 i keys
  have result := wordsAt_key ram pointer (509 + 2 * i.val) (coin.2.1.x.get i) selected
  simpa only [show 509 + 2 * i.val + 1 = 510 + 2 * i.val by omega] using result

/-- Every y-coordinate label pair has its exact offline address. -/
theorem offline_y_key (coin : OfflineCoin) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 0 (offlineSchedule.words coin)) (i : Fin 254) :
    ram (pointer + BitVec.ofNat 256 (1 + 2 * i.val)) = (coin.2.1.y.get i).trueLabel.setWidth 256 ∧
    ram (pointer + BitVec.ofNat 256 (2 + 2 * i.val)) = (coin.2.1.y.get i).falseLabel.setWidth 256 := by
  have keys := inputKey_y_words coin.2.1 ram pointer 1 (offline_inputKey_words coin ram pointer stored)
  have selected := wordsAt_scheduleVector keySchedule 254 coin.2.1.y ram pointer 1 i keys
  have result := wordsAt_key ram pointer (1 + 2 * i.val) (coin.2.1.y.get i) selected
  simpa only [show 1 + 2 * i.val + 1 = 2 + 2 * i.val by omega] using result

end Kriterion.ArgoMAC.ArithmeticSimulator
