import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePointBranch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples GateLoopReady onlineMachineCode

/-- The successful curve source continues with point gates; cutoff ends the request. -/
noncomputable def onlineAfterCurveSamples [BN254.FieldCertificate] (attempts : Nat)
    (result : Bool × Memory × Nat) : PMF (Configuration 290305300 × Nat) :=
  if result.1 then onlinePointBranchSamples attempts result.2.1
  else PMF.pure (⟨290305299, result.2.1⟩, 1)

/-- The valid gate source executes the complete curve phase before the complete point phase. -/
noncomputable def onlineCurvePointSamples [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    PMF (Configuration 290305300 × Nat) :=
  (gateLoopSamples curveGatePlan attempts 1270 0 memory).bind fun result =>
    (onlineAfterCurveSamples attempts result).map fun final => (final.1, final.2 + result.2.2)

/-- Both gate phases execute in their exact source order and retain their actual charges. -/
theorem onlineMachine_curvePointRun [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady curveGatePlan attempts limit 1270 0 memory)
    (later : ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0 memory).support,
      result.1 = true →
        result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 ∧
        GateLoopReady pointGatePlan attempts limit 277368 0 (onlinePointGateInitial result.2.1)) :
    ClosedRun (onlineMachine attempts) 1435662 memory
      (gateDriverRunBudget attempts limit * 1270 +
        (6 + (gateDriverRunBudget attempts limit * 277368 + 200663)))
      (onlineCurvePointSamples attempts memory) := by
  apply sourceContinuation_close (onlineMachine attempts) 1435662 memory
    (gateDriverRunBudget attempts limit * 1270) (6 + (gateDriverRunBudget attempts limit * 277368 + 200663))
    (gateLoopSamples curveGatePlan attempts 1270 0 memory)
    (fun result => ⟨if result.1 then 2751382 else 290305299, result.2.1⟩)
    (fun result => result.2.2) (onlineAfterCurveSamples attempts)
  · intro fuel
    have continued := gateLoopBlock_continue (onlineMachine attempts) curveGatePlan attempts limit (by decide)
      (fun pc => onlineBranchLabels 1435662 1315720 (by decide) 2751382 pc.val)
      (onlineMachine_curveGates attempts) 1270 0 fuel memory (by decide) attemptFits ready
    have label (success : Bool) : onlineBranchLabels 1435662 1315720 (by decide) 2751382
        (gateLoopReturn (count := 1270) (0 + 1270) (by decide) success).val =
          if success then 2751382 else 290305299 := by cases success <;> rfl
    simp only [label] at continued
    exact continued
  · intro result supported
    exact gateLoopSamples_cost curveGatePlan attempts limit 1270 0 memory attemptFits ready result supported
  · intro result supported
    cases success : result.1 with
    | false =>
        simp only [success, Bool.false_eq_true, ↓reduceIte]
        have law := onlineMachine_cutoffClosed attempts
          (6 + (gateDriverRunBudget attempts limit * 277368 + 200663)) result.2.1 (by omega)
        simpa only [onlineAfterCurveSamples, success, Bool.false_eq_true, ↓reduceIte] using law
    | true =>
        simp only [success, ↓reduceIte]
        have law := onlineMachine_pointBranch attempts limit result.2.1 attemptFits
          (later result supported success).1 (later result supported success).2
        simpa only [onlineAfterCurveSamples, success, ↓reduceIte] using law

end Kriterion.ArgoMAC.ArithmeticSimulator
