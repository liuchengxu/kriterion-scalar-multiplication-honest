import Proof.Privacy.Simulator.Arithmetic.CompiledPhaseCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The formal budget covers the complete checked block allowance. -/
theorem compiledBlockAllowance_budget (queries : Nat) : compiledBlockAllowance queries ≤ budget queries := by
  change compiledBlockAllowance queries ≤ 64 * queries ^ 2 + 2 ^ 27 * queries + 2 ^ 46
  exact compiledBlockAllowance_bound queries

/-- The setup charge leaves the chosen-query phase its full prefix allowance. -/
theorem compiledChosenCost_allowance (chosen setupSpent : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2) :
    setupSpent + compiledPublicCost 256 0 chosen ≤ compiledBlockAllowance chosen := by
  have full := compiledPhaseCost_blockAllowance chosen 0 setupSpent 0 setup (by omega)
  simp only [Nat.add_zero, compiledPublicCost, Nat.zero_mul] at full ⊢
  omega

/-- Each chosen-query prefix fits the formal budget at its actual query count. -/
theorem compiledChosenCost_budget (chosen setupSpent : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2) :
    setupSpent + compiledPublicCost 256 0 chosen ≤ budget chosen :=
  (compiledChosenCost_allowance chosen setupSpent setup).trans (compiledBlockAllowance_budget chosen)

/-- The online response fits the block allowance before any decision query occurs. -/
theorem compiledOnlineCost_allowance (chosen setupSpent onlineExecuted : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545) :
    setupSpent + compiledPublicCost 256 0 chosen + (onlineExecuted + 2) ≤ compiledBlockAllowance chosen := by
  simpa only [Nat.add_zero, compiledPublicCost, Nat.zero_mul] using
    compiledPhaseCost_blockAllowance chosen 0 setupSpent onlineExecuted setup online

/-- The online request fits the formal budget at the chosen-query count. -/
theorem compiledOnlineCost_budget (chosen setupSpent onlineExecuted : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545) :
    setupSpent + compiledPublicCost 256 0 chosen + (onlineExecuted + 2) ≤ budget chosen :=
  (compiledOnlineCost_allowance chosen setupSpent onlineExecuted setup online).trans
    (compiledBlockAllowance_budget chosen)

/-- Each decision-query prefix fits the formal budget at its cumulative query count. -/
theorem compiledDecisionCost_budget (chosen decisions initialSpent : Nat)
    (spent : initialSpent ≤ compiledBlockAllowance chosen) :
    initialSpent + compiledPublicCost 256 (chosen + 836423) decisions ≤ budget (chosen + decisions) := by
  have bound := compiledPublicCost_blockAllowance chosen decisions
  rw [Nat.add_comm 836423 chosen] at bound
  exact (Nat.add_le_add_right spent _).trans (bound.trans (compiledBlockAllowance_budget (chosen + decisions)))

/-- The indexed chosen-query coupling needs no extra numerical budget premise. -/
theorem compiledChosenCost_responseBudget (setupSpent used : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2) :
    setupSpent + compiledPublicCost 256 0 (used + 1) ≤ budget (0 + used + 1) := by
  simpa only [Nat.zero_add] using compiledChosenCost_budget (used + 1) setupSpent setup

/-- The indexed decision-query coupling uses the original chosen-prefix count. -/
theorem compiledDecisionCost_responseBudget (chosen initialSpent used : Nat)
    (spent : initialSpent ≤ compiledBlockAllowance chosen) :
    initialSpent + compiledPublicCost 256 (chosen + 836423) (used + 1) ≤ budget (chosen + used + 1) := by
  simpa only [Nat.add_assoc] using compiledDecisionCost_budget chosen (used + 1) initialSpent spent

/-- The complete accepted machine charge satisfies the actual formal budget. -/
theorem compiledPhaseCost_budget (chosen decisions setupSpent chosenSpent onlineExecuted onlineSpent finalSpent : Nat)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (chosenCost : chosenSpent ≤ setupSpent + compiledPublicCost 256 0 chosen)
    (online : onlineExecuted ≤
      2153421270 * 256 + 46833536 * (chosen + 836423) + 6 * chosen + 235015545)
    (onlineCost : onlineSpent ≤ chosenSpent + (onlineExecuted + 2))
    (decisionCost : finalSpent ≤ onlineSpent + compiledPublicCost 256 (chosen + 836423) decisions) :
    finalSpent ≤ budget (chosen + decisions) := by
  change finalSpent ≤ 64 * (chosen + decisions) ^ 2 + 2 ^ 27 * (chosen + decisions) + 2 ^ 46
  exact compiledPhaseCost_spent chosen decisions setupSpent chosenSpent onlineExecuted onlineSpent finalSpent
    setup chosenCost online onlineCost decisionCost

end Kriterion.ArgoMAC.ArithmeticSimulator
