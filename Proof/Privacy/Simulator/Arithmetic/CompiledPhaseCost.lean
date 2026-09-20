import Proof.Privacy.Simulator.Arithmetic.CompiledSetupJoint
import Proof.Privacy.Simulator.Arithmetic.CompiledPublicAllowance
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory offlineSchedule

private theorem setupCostArithmetic (spent size offlineSize sampled serialization : Nat)
    (actual : spent ≤ size + 1 + (sampled + serialization + 5))
    (body : offlineSize + 1 + (sampled + serialization + 3) ≤ 605084290688)
    (table : size + 1 ≤ 2 ^ 30) : spent ≤ 2 ^ 30 + 605084290688 + 2 := by omega

/-- Each setup sample pays for the complete table, sampling, serialization, and dispatch. -/
theorem compiledSetupJoint_fixedCost [BN254.FieldCertificate] (parameter : Nat)
    (state : State) (coin : Security.SimulatorSampling.OfflineCoin)
    (supported : (state, coin) ∈ (compiledSetupJoint 256 parameter).support) :
    state.spent ≤ 2 ^ 30 + 605084290688 + 2 := by
  exact setupCostArithmetic _ _ _ _ _
    (compiledSetupJoint_cost 256 parameter state coin supported) offlineMachine_budget
    (compiledMachine_controlAllowance 256)

/-- The complete phase sum uses the query count that exists before the online request. -/
theorem compiledPhaseCost_blockAllowance (chosen decisions setupSpent onlineExecuted : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545) :
    setupSpent + compiledPublicCost 256 0 chosen + (onlineExecuted + 2) +
        compiledPublicCost 256 (chosen + 836423) decisions ≤
      compiledBlockAllowance (chosen + decisions) := by
  rw [compiledBlockAllowance_expanded]
  unfold compiledPublicCost
  nlinarith

/-- The final polynomial covers all actual setup, chosen-query, online, and decision costs. -/
theorem compiledPhaseCost_polynomial (chosen decisions setupSpent onlineExecuted : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545) :
    setupSpent + compiledPublicCost 256 0 chosen + (onlineExecuted + 2) +
        compiledPublicCost 256 (chosen + 836423) decisions ≤
      64 * (chosen + decisions) ^ 2 + 2 ^ 27 * (chosen + decisions) + 2 ^ 46 :=
  (compiledPhaseCost_blockAllowance chosen decisions setupSpent onlineExecuted setup online).trans
    (compiledBlockAllowance_bound (chosen + decisions))

/-- Each accepted cumulative charge fits the complete actual phase sum. -/
theorem compiledPhaseCost_spent (chosen decisions setupSpent chosenSpent onlineExecuted onlineSpent finalSpent : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (chosenCost : chosenSpent ≤ setupSpent + compiledPublicCost 256 0 chosen)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545)
    (onlineCost : onlineSpent ≤ chosenSpent + (onlineExecuted + 2))
    (decisionCost : finalSpent ≤ onlineSpent + compiledPublicCost 256 (chosen + 836423) decisions) :
    finalSpent ≤ 64 * (chosen + decisions) ^ 2 + 2 ^ 27 * (chosen + decisions) + 2 ^ 46 := by
  apply le_trans (show finalSpent ≤ setupSpent + compiledPublicCost 256 0 chosen +
    (onlineExecuted + 2) + compiledPublicCost 256 (chosen + 836423) decisions by omega)
  exact compiledPhaseCost_polynomial chosen decisions setupSpent onlineExecuted setup online

/-- The valid online body has the required bound at the actual chosen-query count. -/
theorem onlineMachine_validPrefixCost [BN254.FieldCertificate] (chosen limit : Nat)
    (state : SparseOracleFamily) (output : BN254.Point)
    (count : limit ≤ chosen + 836423) (hashes : state.hash.length ≤ chosen) :
    onlinePrefixCost (some output) +
      (3 + (1 + (onlineSamplingBudget 256 + onlineSelectedReserve 256 limit state))) ≤
        2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545 := by
  have cost := onlineMachine_validCost 256 limit state output
  omega

/-- The absent-output body has the same bound at the actual chosen-query count. -/
theorem onlineMachine_nullPrefixCost [BN254.FieldCertificate] (chosen limit : Nat)
    (state : SparseOracleFamily) (count : limit ≤ chosen + 836423) (hashes : state.hash.length ≤ chosen) :
    onlinePrefixCost none + (6 + (gateDriverRunBudget 256 limit * 1270 + 200666)) ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545 := by
  have cost := onlineMachine_nullCost 256 limit state
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
