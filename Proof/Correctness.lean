import Proof.Correctness.Base7Termination
import Proof.Correctness.RCBComplete

namespace Kriterion.ArgoMAC

open BN254

/-- The circuit function equals the required scalar multiplication function. -/
theorem functionCorrect [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (input : AffineInput) :
    (Garbling.garbledCircuit construction).function scalar input =
      checkedScalarMultiplication scalar.value input := rfl

/-- Every random tape gives the required evaluation result. -/
theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness (Garbling.garbledCircuit construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  RCBComplete.perfectCorrectness

end Kriterion.ArgoMAC
