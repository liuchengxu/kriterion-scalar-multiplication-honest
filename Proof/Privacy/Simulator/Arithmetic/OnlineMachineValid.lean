import Proof.Privacy.Simulator.Arithmetic.OnlineMachineSampled
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineInputFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- Every supplied point has a nonzero protocol tag. -/
theorem onlineOutputWords_present [BN254.FieldCertificate] (output : BN254.Point) :
    BitVec.ofNat 256 (onlineOutputWords (some output)).1 ≠ (0 : Word) := by
  cases output <;> simp only [onlineOutputWords] <;> decide

/-- The valid branch source charges its tag test before the private and public phases. -/
noncomputable def onlineValidBranchSamples [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (onlineValidBodySamples attempts (onlineTagMemory memory) output state key suffix).map
    fun result => (result.1, result.2 + 3)

/-- The actual valid branch enters the complete selected source. -/
theorem onlineMachine_validBranch [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0)
    (ready : OnlineSampledReady attempts limit (onlineTagMemory memory) output state key suffix) :
    ClosedRun (onlineMachine attempts) 13618 memory
      (3 + (1 + (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit state)))
      (onlineValidBranchSamples attempts memory output state key suffix) := by
  have branch : FixedContinuation (onlineMachine attempts) 13618 13621 memory (onlineTagMemory memory) 3 := by
    intro fuel
    have law := onlineMachine_firstBranch_continue attempts fuel memory
    simp only [onlineBranchReturn, if_neg present] at law
    exact law
  exact branch.close _ _ _ _ _ _ _ _
    (onlineMachine_validBody attempts limit (onlineTagMemory memory) output state key suffix attemptFits ready)

/-- The full valid source includes the parsed input and common curve preparation. -/
noncomputable def onlineValidSamples [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (input : BN254.AffineInput) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (onlineValidBranchSamples attempts (onlineCurveMemory memory input (some output) suffix) output state key suffix).map
    fun result => (result.1, result.2 + onlinePrefixCost (some output))

/-- The actual valid machine has one source law from its input entry through its final halt. -/
theorem onlineMachine_valid [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : BN254.AffineInput) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (wire : memory.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output (some output) ++ suffix)
    (attemptFits : attempts < 2 ^ 256)
    (ready : OnlineSampledReady attempts limit
      (onlineTagMemory (onlineCurveMemory memory input (some output) suffix)) output state key suffix) :
    ClosedRun (onlineMachine attempts) 0 memory
      (onlinePrefixCost (some output) +
        (3 + (1 + (onlineSamplingBudget attempts + onlineSelectedReserve attempts limit state))))
      (onlineValidSamples attempts memory input output state key suffix) := by
  have present : (onlineCurveMemory memory input (some output) suffix).ram
      (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 := by
    rw [onlineCurveMemory_tag]
    exact onlineOutputWords_present output
  exact (onlineMachine_prefix attempts memory input (some output) suffix wire).close _ _ _ _ _ _ _ _
    (onlineMachine_validBranch attempts limit (onlineCurveMemory memory input (some output) suffix)
      output state key suffix attemptFits present ready)

end Kriterion.ArgoMAC.ArithmeticSimulator
