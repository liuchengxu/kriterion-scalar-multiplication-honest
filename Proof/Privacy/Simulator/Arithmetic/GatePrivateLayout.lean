import Proof.Privacy.Simulator.Arithmetic.GateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling

/-- Each private target word has its exact sampled field value. -/
theorem gateArrays_target (coefficients gates : Nat) (data : GateArrays coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateArraysSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256 (start + coordinateBitCount * gate.val + index.val)) =
      BitVec.ofNat 256 ((data.2.2.2.get gate).get index).val := by
  simp only [gateArraysSchedule, privateSchedule_cast_words] at stored
  have rest := wordsAt_pair_right (fieldSchedule.vector coefficients)
    (((tableSchedule.vector coordinateBitCount).vector gates).pair
      (((quotientSchedule.vector coordinateBitCount).vector gates).pair
        ((fieldSchedule.vector coordinateBitCount).vector gates))) ram pointer start data stored
  have tail := wordsAt_pair_right ((tableSchedule.vector coordinateBitCount).vector gates)
    (((quotientSchedule.vector coordinateBitCount).vector gates).pair
      ((fieldSchedule.vector coordinateBitCount).vector gates)) ram pointer start data.2 rest
  have targets := wordsAt_pair_right ((quotientSchedule.vector coordinateBitCount).vector gates)
    ((fieldSchedule.vector coordinateBitCount).vector gates) ram pointer start data.2.2 tail
  have row := wordsAt_scheduleVector (fieldSchedule.vector coordinateBitCount) gates data.2.2.2 ram pointer start gate targets
  have word := wordsAt_scheduleVector fieldSchedule coordinateBitCount (data.2.2.2.get gate) ram pointer _ index row
  simpa only [Nat.mul_one, Nat.one_mul] using wordsAt_field ram pointer _ ((data.2.2.2.get gate).get index) word

/-- The function source has the same canonical target positions. -/
theorem gateData_target (coefficients gates : Nat) (data : GateData coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateDataSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256 (start + coordinateBitCount * gate.val + index.val)) =
      BitVec.ofNat 256 (data.2.2.2 gate index).val := by
  simpa [gateArraysEquiv, Security.vectorFunctionEquiv, Vector.get, Fin.cast] using gateArrays_target coefficients gates
    ((gateArraysEquiv coefficients gates).symm data) ram pointer start gate index stored

end Kriterion.ArgoMAC.ArithmeticSimulator
