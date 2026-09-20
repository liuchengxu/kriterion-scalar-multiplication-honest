import Proof.Privacy.Simulator.Arithmetic.FixedContinuation
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples GateLoopReady onlineMachineCode

/-- The point source returns original labels or the public-sampler cutoff state. -/
noncomputable def onlinePointGateResult (result : Bool × Memory × Nat) : Configuration 290305300 × Nat :=
  if result.1 then (⟨290305298, onlineFinalMemory result.2.1⟩, result.2.2 + 200663)
  else (⟨290305299, result.2.1⟩, result.2.2 + 1)

/-- The actual point gate loop closes its exact source and final original-label output. -/
theorem onlineMachine_pointGateRun [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady pointGatePlan attempts limit 277368 0 memory) :
    ClosedRun (onlineMachine attempts) 2751388 memory
      (gateDriverRunBudget attempts limit * 277368 + 200663)
      ((gateLoopSamples pointGatePlan attempts 277368 0 memory).map onlinePointGateResult) := by
  intro fuel
  have continued := gateLoopBlock_continue (onlineMachine attempts) pointGatePlan attempts limit (by decide)
    (fun pc => onlineBranchLabels 2751388 287353248 (by decide) 290104636 pc.val)
    (onlineMachine_pointGates attempts) 277368 0 (200663 + fuel) memory (by decide) attemptFits ready
  change run (onlineMachine attempts) (gateDriverRunBudget attempts limit * 277368 + (200663 + fuel))
    ⟨2751388, memory⟩ = _ at continued
  rw [Nat.add_assoc, continued, PMF.map_comp, ← PMF.bind_pure_comp]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bound := gateLoopSamples_cost pointGatePlan attempts limit 277368 0 memory attemptFits ready result supported
  cases success : result.1 with
  | false =>
      have label : onlineBranchLabels 2751388 287353248 (by decide) 290104636
          (gateLoopReturn (count := 277368) (0 + 277368) (by decide) false).val = 290305299 := rfl
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 277368 + (200663 + fuel) - result.2.2 =
          1 + (gateDriverRunBudget attempts limit * 277368 + 200662 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_cutoff, PMF.pure_map]
      simp only [onlinePointGateResult, success, Bool.false_eq_true, ↓reduceIte, Function.comp_apply,
        Option.map_some, Nat.add_comm]
  | true =>
      have label : onlineBranchLabels 2751388 287353248 (by decide) 290104636
          (gateLoopReturn (count := 277368) (0 + 277368) (by decide) true).val = 290104636 := rfl
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 277368 + (200663 + fuel) - result.2.2 =
          200663 + (gateDriverRunBudget attempts limit * 277368 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_finish, PMF.pure_map]
      simp only [onlinePointGateResult, success, ↓reduceIte, Function.comp_apply, Option.map_some, Nat.add_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
