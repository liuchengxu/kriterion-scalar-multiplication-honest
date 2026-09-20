import Proof.Privacy.Simulator.Arithmetic.PrivateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling

/-- Each gate array coefficient follows all target, quotient, and table words. -/
theorem gateArrays_coefficient (coefficients gates : Nat) (data : GateArrays coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat) (index : Fin coefficients)
    (stored : WordsAt ram pointer start ((gateArraysSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256 (start + 3 * gates * coordinateBitCount + index.val)) =
      BitVec.ofNat 256 (data.1.get index).val := by
  simp only [gateArraysSchedule, privateSchedule_cast_words] at stored
  have selected := wordsAt_pair_left (fieldSchedule.vector coefficients)
    (((tableSchedule.vector coordinateBitCount).vector gates).pair
      (((quotientSchedule.vector coordinateBitCount).vector gates).pair
        ((fieldSchedule.vector coordinateBitCount).vector gates))) ram pointer start data stored
  have word := wordsAt_scheduleVector fieldSchedule coefficients data.1 ram pointer _ index selected
  have value := wordsAt_field ram pointer _ (data.1.get index) word
  have address : start + (gates * (coordinateBitCount * 1) + gates * (coordinateBitCount * 1) +
      gates * (coordinateBitCount * 1)) + 1 * index.val =
      start + 3 * gates * coordinateBitCount + index.val := by ring
  simpa only [address] using value

/-- Each gate ciphertext follows all target and quotient words. -/
theorem gateArrays_table (coefficients gates : Nat) (data : GateArrays coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateArraysSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256
      (start + 2 * gates * coordinateBitCount + coordinateBitCount * gate.val + index.val)) =
      ((data.2.1.get gate).get index).trueRow := by
  simp only [gateArraysSchedule, privateSchedule_cast_words] at stored
  have rest := wordsAt_pair_right (fieldSchedule.vector coefficients)
    (((tableSchedule.vector coordinateBitCount).vector gates).pair
      (((quotientSchedule.vector coordinateBitCount).vector gates).pair
        ((fieldSchedule.vector coordinateBitCount).vector gates))) ram pointer start data stored
  have tables := wordsAt_pair_left ((tableSchedule.vector coordinateBitCount).vector gates)
    (((quotientSchedule.vector coordinateBitCount).vector gates).pair
      ((fieldSchedule.vector coordinateBitCount).vector gates)) ram pointer start data.2 rest
  have row := wordsAt_scheduleVector (tableSchedule.vector coordinateBitCount) gates data.2.1
    ram pointer _ gate tables
  have word := wordsAt_scheduleVector tableSchedule coordinateBitCount (data.2.1.get gate)
    ram pointer _ index row
  have value := wordsAt_table ram pointer _ ((data.2.1.get gate).get index) word
  have address : start + (gates * (coordinateBitCount * 1) + gates * (coordinateBitCount * 1)) +
      coordinateBitCount * 1 * gate.val + 1 * index.val =
      start + 2 * gates * coordinateBitCount + coordinateBitCount * gate.val + index.val := by ring
  simpa only [address] using value

/-- The function view has the same canonical coefficient positions. -/
theorem gateData_coefficient (coefficients gates : Nat) (data : GateData coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat) (index : Fin coefficients)
    (stored : WordsAt ram pointer start ((gateDataSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256 (start + 3 * gates * coordinateBitCount + index.val)) =
      BitVec.ofNat 256 (data.1 index).val := by
  simpa [gateArraysEquiv, Security.vectorFunctionEquiv, Vector.get, Fin.cast] using gateArrays_coefficient coefficients gates ((gateArraysEquiv coefficients gates).symm data)
    ram pointer start index stored

/-- The function view has the same complete ciphertext positions. -/
theorem gateData_table (coefficients gates : Nat) (data : GateData coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateDataSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256
      (start + 2 * gates * coordinateBitCount + coordinateBitCount * gate.val + index.val)) =
      ((data.2.1 gate).get index).trueRow := by
  simpa [gateArraysEquiv, Security.vectorFunctionEquiv, Vector.get, Fin.cast] using gateArrays_table coefficients gates ((gateArraysEquiv coefficients gates).symm data)
    ram pointer start gate index stored

end Kriterion.ArgoMAC.ArithmeticSimulator
