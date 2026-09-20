import Proof.Privacy.Simulator.Arithmetic.OfflineMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineMachine
import Construction.Simulator.RecordedPublicHandler
import Proof.Privacy.Simulator.Arithmetic.PhaseMachineRun

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan

private theorem compiledSizeBound (wire : Nat)
    (bound : wire + 1 + (wire + 1) ≤ 477065504) :
    (2 + 39 * 838208 + wire) + 290305299 + 1809 + 6 + 1 ≤ 600000000 := by omega

private theorem compiledSizeFits (size : Nat) (bound : size + 1 ≤ 600000000) :
    size < 2 ^ 256 := by omega

/-- The complete table fits in the machine address space. -/
theorem compiledMachine_fits (attempts : Nat) :
    phaseMachineSize (offlineMachine attempts) (onlineMachine attempts)
      (recordedPublicHandler attempts) < 2 ^ 256 := by
  apply compiledSizeFits
  exact compiledSizeBound publicWireProgram.length publicWireMachine_budget

/-- The simulator uses one fixed table for all three request types. -/
def compiledMachine (attempts : Nat) : Machine :=
  phaseMachine (offlineMachine attempts) (onlineMachine attempts)
    (recordedPublicHandler attempts) (compiledMachine_fits attempts)

/-- The fixed table has fewer than six hundred million entries. -/
theorem compiledMachine_tableCost (attempts : Nat) :
    (compiledMachine attempts).size + 1 ≤ 600000000 := by
  exact compiledSizeBound publicWireProgram.length publicWireMachine_budget

/-- The reserved control allowance covers the fixed table charge. -/
theorem compiledMachine_controlAllowance (attempts : Nat) :
    (compiledMachine attempts).size + 1 ≤ 2 ^ 30 :=
  (compiledMachine_tableCost attempts).trans (by decide)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
