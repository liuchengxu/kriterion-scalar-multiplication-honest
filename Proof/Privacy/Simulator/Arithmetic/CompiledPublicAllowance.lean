import Proof.Privacy.Simulator.Arithmetic.CompiledProgramCoupling
import Proof.Privacy.Simulator.Arithmetic.CompiledBlockAllowance

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The block allowance pays for a later public phase at its cumulative table count. -/
theorem compiledPublicCost_blockAllowance (initialQueries used : Nat) :
    compiledBlockAllowance initialQueries + compiledPublicCost 256 (836423 + initialQueries) used ≤
      compiledBlockAllowance (initialQueries + used) := by
  simp only [compiledBlockAllowance_expanded, compiledPublicCost]
  nlinarith

/-- The rounded polynomial covers the public phase and the previous block allowance. -/
theorem compiledPublicCost_polynomial (initialQueries used initialSpent : Nat)
    (spent : initialSpent ≤ compiledBlockAllowance initialQueries) :
    initialSpent + compiledPublicCost 256 (836423 + initialQueries) used ≤
      64 * (initialQueries + used) ^ 2 + 2 ^ 27 * (initialQueries + used) + 2 ^ 46 := by
  exact (Nat.add_le_add_right spent _).trans
    ((compiledPublicCost_blockAllowance initialQueries used).trans
      (compiledBlockAllowance_bound (initialQueries + used)))

/-- The small-query condition supplies room for every call in the public phase. -/
theorem compiledPublicCost_room (initialQueries total : Nat)
    (small : initialQueries + total < 2 ^ 101) :
    256 + 2 * ((836423 + initialQueries) + total) < 2 ^ 110 := by
  have room := oracleTable_capacity (initialQueries + total) small
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
