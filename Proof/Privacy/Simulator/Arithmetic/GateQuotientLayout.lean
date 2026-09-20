import Proof.Privacy.Simulator.Arithmetic.GatePrivateLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling

/-- The quotient source stores its finite integer as one word. -/
theorem wordsAt_quotient (ram : Word → Word) (pointer : Word) (start : Nat)
    (value : Security.HashLiftQuotient) (stored : WordsAt ram pointer start (quotientSchedule.words value)) :
    ram (pointer + BitVec.ofNat 256 start) = BitVec.ofNat 256 value.val := by
  simpa only [Nat.add_zero, quotientSchedule, PrivateSchedule.primitive, List.getElem_cons_zero] using
    stored 0 (by rw [quotientSchedule.wordsLength]; decide)

/-- Each private quotient follows the complete target region. -/
theorem gateArrays_quotient (coefficients gates : Nat) (data : GateArrays coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateArraysSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256
      (start + gates * coordinateBitCount + coordinateBitCount * gate.val + index.val)) =
      BitVec.ofNat 256 ((data.2.2.1.get gate).get index).val := by
  simp only [gateArraysSchedule, privateSchedule_cast_words] at stored
  have rest := wordsAt_pair_right (fieldSchedule.vector coefficients)
    (((tableSchedule.vector coordinateBitCount).vector gates).pair
      (((quotientSchedule.vector coordinateBitCount).vector gates).pair
        ((fieldSchedule.vector coordinateBitCount).vector gates))) ram pointer start data stored
  have tail := wordsAt_pair_right ((tableSchedule.vector coordinateBitCount).vector gates)
    (((quotientSchedule.vector coordinateBitCount).vector gates).pair
      ((fieldSchedule.vector coordinateBitCount).vector gates)) ram pointer start data.2 rest
  have quotients := wordsAt_pair_left ((quotientSchedule.vector coordinateBitCount).vector gates)
    ((fieldSchedule.vector coordinateBitCount).vector gates) ram pointer start data.2.2 tail
  have row := wordsAt_scheduleVector (quotientSchedule.vector coordinateBitCount) gates data.2.2.1
    ram pointer _ gate quotients
  have word := wordsAt_scheduleVector quotientSchedule coordinateBitCount (data.2.2.1.get gate)
    ram pointer _ index row
  simpa only [Nat.mul_one, Nat.one_mul] using
    wordsAt_quotient ram pointer _ ((data.2.2.1.get gate).get index) word

/-- The function source uses the same quotient addresses. -/
theorem gateData_quotient (coefficients gates : Nat) (data : GateData coefficients gates)
    (ram : Word → Word) (pointer : Word) (start : Nat)
    (gate : Fin gates) (index : Fin coordinateBitCount)
    (stored : WordsAt ram pointer start ((gateDataSchedule coefficients gates).words data)) :
    ram (pointer + BitVec.ofNat 256
      (start + gates * coordinateBitCount + coordinateBitCount * gate.val + index.val)) =
      BitVec.ofNat 256 (data.2.2.1 gate index).val := by
  simpa [gateArraysEquiv, Security.vectorFunctionEquiv, Vector.get, Fin.cast] using gateArrays_quotient coefficients gates
    ((gateArraysEquiv coefficients gates).symm data) ram pointer start gate index stored

end Kriterion.ArgoMAC.ArithmeticSimulator
