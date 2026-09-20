import Proof.Privacy.Simulator.Arithmetic.FixedContinuation
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineBranch
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The absent-output tail emits the original labels after its tag test. -/
theorem onlineMachine_nullFinish [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory)
    (absent : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    run (onlineMachine attempts) (200666 + fuel) ⟨2751382, memory⟩ =
      PMF.pure (some (⟨290305298, onlineFinalMemory (onlineTagMemory memory)⟩, 200666)) := by
  have branch : FixedContinuation (onlineMachine attempts) 2751382 290104636 memory (onlineTagMemory memory) 3 := by
    intro reserve
    have law := onlineMachine_secondBranch_continue attempts reserve memory
    simp only [onlineBranchReturn, absent, ↓reduceIte] at law
    exact law
  have output : ClosedRun (onlineMachine attempts) 290104636 (onlineTagMemory memory) 200663
      (PMF.pure (⟨290305298, onlineFinalMemory (onlineTagMemory memory)⟩, 200663)) := by
    intro reserve
    simpa only [PMF.pure_map] using onlineMachine_finish attempts reserve (onlineTagMemory memory)
  have result := branch.close _ _ _ _ _ _ _ _ output fuel
  simpa only [PMF.pure_map] using result

end Kriterion.ArgoMAC.ArithmeticSimulator
