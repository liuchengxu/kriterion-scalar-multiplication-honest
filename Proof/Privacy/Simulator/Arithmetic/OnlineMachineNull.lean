import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNullGates
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineInputFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
attribute [local irreducible] gateLoopSamples GateLoopReady

/-- The absent-output gate phase uses the original-label buffer. -/
def onlineNullGateInitial (memory : Memory) : Memory :=
  executeLinear onlineOriginalSetup (onlineTagMemory memory)

/-- The absent-output branch runs the curve setup and the complete curve source. -/
theorem onlineMachine_nullBranch [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (absent : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0)
    (ready : GateLoopReady curveGatePlan attempts limit 1270 0 (onlineNullGateInitial memory))
    (kept : ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0 (onlineNullGateInitial memory)).support,
      result.1 = true → result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    ClosedRun (onlineMachine attempts) 13618 memory
      (6 + (gateDriverRunBudget attempts limit * 1270 + 200666))
      (((gateLoopSamples curveGatePlan attempts 1270 0 (onlineNullGateInitial memory)).map onlineNullGateResult).map
        fun result => (result.1, result.2 + 6)) := by
  have branch : FixedContinuation (onlineMachine attempts) 13618 1435659 memory (onlineTagMemory memory) 3 := by
    intro reserve
    have law := onlineMachine_firstBranch_continue attempts reserve memory
    simp only [onlineBranchReturn, absent, ↓reduceIte] at law
    exact law
  have setup : FixedContinuation (onlineMachine attempts) 1435659 1435662
      (onlineTagMemory memory) (onlineNullGateInitial memory) 3 := by
    intro reserve
    exact linear_continue (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 1435659 3 (by decide) 1435662) (onlineMachine_curveSetup attempts)
      (onlineTagMemory memory) reserve
  exact (branch.trans _ _ _ _ _ _ _ _ _ setup).close _ _ _ _ _ _ _ _
    (onlineMachine_nullGates attempts limit (onlineNullGateInitial memory) attemptFits ready kept)

/-- The absent-output machine has one exact source law from its input entry to its halt. -/
theorem onlineMachine_null [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (input : BN254.AffineInput) (rest : List Bool)
    (wire : memory.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output none ++ rest)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady curveGatePlan attempts limit 1270 0
      (onlineNullGateInitial (onlineCurveMemory memory input none rest)))
    (kept : ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0
      (onlineNullGateInitial (onlineCurveMemory memory input none rest))).support,
      result.1 = true → result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    ClosedRun (onlineMachine attempts) 0 memory
      (onlinePrefixCost none + (6 + (gateDriverRunBudget attempts limit * 1270 + 200666)))
      ((((gateLoopSamples curveGatePlan attempts 1270 0
        (onlineNullGateInitial (onlineCurveMemory memory input none rest))).map onlineNullGateResult).map
          fun result => (result.1, result.2 + 6)).map
            fun result => (result.1, result.2 + onlinePrefixCost none)) :=
  (onlineMachine_prefix attempts memory input none rest wire).close _ _ _ _ _ _ _ _
    (onlineMachine_nullBranch attempts limit (onlineCurveMemory memory input none rest) attemptFits
      (onlineCurveMemory_tag memory input none rest) ready kept)

/-- The absent-output reserve has one exact scalar bound. -/
theorem onlineMachine_null_cost [BN254.FieldCertificate] (attempts limit : Nat) :
    onlinePrefixCost none + (6 + (gateDriverRunBudget attempts limit * 1270 + 200666)) =
      gateDriverRunBudget attempts limit * 1270 + 217800 := by
  change 1 + ((3608 - 1) + (3 + (7112 + 6405))) +
    (6 + (gateDriverRunBudget attempts limit * 1270 + 200666)) = _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
