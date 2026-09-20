import Proof.Privacy.Simulator.Arithmetic.GateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The offline source stores the public sample after the bridge key and input keys. -/
theorem offline_public_words (coin : OfflineCoin) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 0 (offlineSchedule.words coin)) :
    WordsAt ram pointer 1017 (publicSchedule.words coin.1) := by
  exact wordsAt_pair_left publicSchedule (inputKeySchedule.pair fieldSchedule) ram pointer 0 coin stored

/-- The curve sample follows all 91 public point rows. -/
theorem public_curve_words (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    WordsAt ram pointer 834395 ((gateDataSchedule 3 5).words
      (sample.curve.coefficients, sample.curve.tables, sample.curve.quotients, sample.curve.targets)) := by
  exact wordsAt_pair_left ((gateDataSchedule 3 5).equiv curveEquiv)
    (rowSchedule.vector FieldMacToECMac.outputMacCount) ram pointer 1017
    (sample.curve, sample.points) stored

/-- Each public row occupies exactly 9158 source words. -/
theorem public_row_words (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (row : Fin FieldMacToECMac.outputMacCount)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    WordsAt ram pointer (1017 + 9158 * row.val) (rowSchedule.words (sample.points.get row)) := by
  have rows := wordsAt_pair_right ((gateDataSchedule 3 5).equiv curveEquiv)
    (rowSchedule.vector FieldMacToECMac.outputMacCount) ram pointer 1017
    (sample.curve, sample.points) stored
  exact wordsAt_scheduleVector rowSchedule FieldMacToECMac.outputMacCount sample.points
    ram pointer 1017 row rows

/-- The X gate data starts after the Z and Y data of one row. -/
theorem row_x_words (sample : RowPublicSample) (ram : Word → Word) (pointer : Word) (start : Nat)
    (stored : WordsAt ram pointer start (rowSchedule.words sample)) :
    WordsAt ram pointer (start + 6105) ((gateDataSchedule 5 4).words
      (sample.x.coefficients, sample.x.tables, sample.x.quotients, sample.x.targets)) := by
  exact wordsAt_pair_left ((gateDataSchedule 5 4).equiv xEquiv)
    (((gateDataSchedule 4 3).equiv yEquiv).pair ((gateDataSchedule 5 5).equiv zEquiv))
    ram pointer start (sample.x, sample.y, sample.z) stored

/-- The Y gate data starts after the Z data of one row. -/
theorem row_y_words (sample : RowPublicSample) (ram : Word → Word) (pointer : Word) (start : Nat)
    (stored : WordsAt ram pointer start (rowSchedule.words sample)) :
    WordsAt ram pointer (start + 3815) ((gateDataSchedule 4 3).words
      (sample.y.coefficients, sample.y.tables, sample.y.quotients, sample.y.targets)) := by
  have rest := wordsAt_pair_right ((gateDataSchedule 5 4).equiv xEquiv)
    (((gateDataSchedule 4 3).equiv yEquiv).pair ((gateDataSchedule 5 5).equiv zEquiv))
    ram pointer start (sample.x, sample.y, sample.z) stored
  exact wordsAt_pair_left ((gateDataSchedule 4 3).equiv yEquiv) ((gateDataSchedule 5 5).equiv zEquiv)
    ram pointer start (sample.y, sample.z) rest

/-- The Z gate data starts at the first word of its row. -/
theorem row_z_words (sample : RowPublicSample) (ram : Word → Word) (pointer : Word) (start : Nat)
    (stored : WordsAt ram pointer start (rowSchedule.words sample)) :
    WordsAt ram pointer start ((gateDataSchedule 5 5).words
      (sample.z.coefficients, sample.z.tables, sample.z.quotients, sample.z.targets)) := by
  have rest := wordsAt_pair_right ((gateDataSchedule 5 4).equiv xEquiv)
    (((gateDataSchedule 4 3).equiv yEquiv).pair ((gateDataSchedule 5 5).equiv zEquiv))
    ram pointer start (sample.x, sample.y, sample.z) stored
  exact wordsAt_pair_right ((gateDataSchedule 4 3).equiv yEquiv) ((gateDataSchedule 5 5).equiv zEquiv)
    ram pointer start (sample.y, sample.z) rest

end Kriterion.ArgoMAC.ArithmeticSimulator
