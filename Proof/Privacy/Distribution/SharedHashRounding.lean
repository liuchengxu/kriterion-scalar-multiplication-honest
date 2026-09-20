import Proof.Privacy.Source.SharedFullSourceTape
import Proof.Privacy.Distribution.HashDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- Full hash rounding keeps the actual shared retained tape distribution unchanged. -/
theorem sharedRetainedHashRounding_observation_bound [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (retained : PMF SharedMaskRetainedTape)
    (observe : SharedMaskRetainedTape → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → PMF Observation)
    (event : Set Observation) :
    |((retained.bind fun source =>
        (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
          (observe source)).toOuterMeasure event).toReal -
      ((retained.bind fun source =>
        (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
          (fun pair => observe source ((fun gate => goodHashLiftSource (pair.1 gate)), pair.2))).toOuterMeasure
            event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  rw [PMF.bind_comm retained (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)),
    PMF.bind_comm retained (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest))]
  have bound := hashLift_family_product_observation_bound
    (fun pair => retained.bind fun source => observe source pair) event
  have count : (Fintype.card RawCircuitGate : ℝ) = 278638 := by
    exact_mod_cast rawCircuitGate_card
  simpa only [count] using bound

end
end Kriterion.ArgoMAC.Security
