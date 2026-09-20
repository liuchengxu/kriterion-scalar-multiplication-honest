import Proof.Privacy.Simulator.Arithmetic.OnlineMachineValid
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNull
import Proof.Privacy.Simulator.Arithmetic.OnlineSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The parsed common prefix has one uniform deterministic allowance. -/
theorem onlinePrefixCost_bound [BN254.FieldCertificate] (output : Option BN254.Point) :
    onlinePrefixCost output ≤ 20695 := by
  have input := onlineInput_budget output
  change 98 + onlineInputCost output ≤ 7273 at input
  unfold onlinePrefixCost
  omega

attribute [local irreducible] onlineSamplingBudget onlinePrefixCost

private theorem validCostArithmetic (prefixCost sampled attempts limit hashes : Nat)
    (prefixBound : prefixCost ≤ 20695)
    (sampleBound : sampled + 1 + 8771 + 1 ≤ 183 * (2574 * attempts) + 151935) :
    prefixCost + (3 + (1 + (sampled + (1678841 +
      (6 * hashes + 9056 + 508 * (2574 * attempts + 44 * (limit + 508) + 274) +
      ((3 * (8 + (2574 * attempts + 56 * limit + 206)) + 84) * 278638 + 200672)))))) ≤
      2153421270 * attempts + 46833536 * limit + 6 * hashes + 235015545 := by
  ring_nf at sampleBound ⊢
  omega

/-- The complete valid request has an explicit arithmetic-operation polynomial. -/
theorem onlineMachine_validCost [BN254.FieldCertificate] (attempts limit : Nat)
    (state : SparseOracleFamily) (output : BN254.Point) :
    onlinePrefixCost (some output) +
        (3 + (1 + (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit state))) ≤
      2153421270 * attempts + 46833536 * limit + 6 * state.hash.length + 235015545 := by
  have prefixBound := onlinePrefixCost_bound (some output)
  have sampled := onlineSampling_cost attempts
  rw [show (onlineSampling attempts).size = 8771 from rfl] at sampled
  rw [onlineSelectedReserve, onlineGateReserve_eq]
  unfold gateDriverRunBudget gateSlotBudget checkedSlotRunBudget encLinkLoopBudget encLinkRowBudget
  exact validCostArithmetic _ _ _ _ _ prefixBound sampled

/-- The complete absent-output request fits the same arithmetic-operation polynomial. -/
theorem onlineMachine_nullCost [BN254.FieldCertificate] (attempts limit : Nat) (state : SparseOracleFamily) :
    onlinePrefixCost none + (6 + (gateDriverRunBudget attempts limit * 1270 + 200666)) ≤
      2153421270 * attempts + 46833536 * limit + 6 * state.hash.length + 235015545 := by
  rw [onlineMachine_null_cost]
  unfold gateDriverRunBudget gateSlotBudget checkedSlotRunBudget
  omega

/-- The instruction table adds its exact fixed size to the common request polynomial. -/
theorem onlineMachine_tableCost (attempts limit : Nat) (state : SparseOracleFamily) :
    (onlineMachine attempts).size + 1 +
        (2153421270 * attempts + 46833536 * limit + 6 * state.hash.length + 235015545) =
      2153421270 * attempts + 46833536 * limit + 6 * state.hash.length + 525320845 := by
  change 290305300 + _ = _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
