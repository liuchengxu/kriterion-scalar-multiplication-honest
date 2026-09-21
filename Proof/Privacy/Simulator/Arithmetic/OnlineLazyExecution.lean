import Proof.Privacy.Simulator.Arithmetic.OnlineLazyRun
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine
noncomputable section
set_option maxRecDepth 4096

/-- The valid source includes the parsed input and its branch cost. -/
def lazyOnlineValidResult [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF (Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat)) :=
  (lazyOnlineValidBodyResult (onlineTagMemory (onlineCurveMemory memory input (some output) [])) output oracle).map
    (Option.map fun result => (result.1, result.2.1, result.2.2 + 3 + onlinePrefixCost (some output)))

/-- The valid execution uses the finite private source and strict oracle programming. -/
theorem lazyOnlineMachine_valid [FieldCertificate] [GroupCertificate]
    (fuel : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (wire : memory.bits 0 = GarbledCircuit.SimulatorProtocol.affine input ++
      GarbledCircuit.SimulatorProtocol.output (some output)) :
    lazyOnlineMachine.run (onlinePrefixCost (some output) + 3 +
      (1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672))) + fuel)
      ⟨0, memory⟩ oracle =
      (lazyOnlineValidResult memory input output oracle).map
        (Option.map fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2)) := by
  have present : (onlineCurveMemory memory input (some output) []).ram
      (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 := by
    rw [onlineCurveMemory_tag]
    exact onlineOutputWords_present output
  rw [show onlinePrefixCost (some output) + 3 +
      (1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672))) + fuel =
      onlinePrefixCost (some output) + (3 +
        ((1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672))) + fuel)) by omega,
    lazyOnlineMachine_prefix_run memory input (some output) [] (by simpa using wire),
    lazyOnlineMachine_firstBranch_continue]
  simp only [onlineBranchReturn, present, if_false]
  rw [lazyOnlineMachine_validBody _ _ output oracle
    (lazyOnline_sampled_selected memory input output)
    (fun sampled supported => lazyOnline_linked_ready memory input output sampled supported oracle)]
  simp [lazyOnlineValidResult, PMF.map_comp, Option.map_map, Function.comp_def]

/-- The online source selects the branch from the supplied output. -/
def lazyOnlineResult [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Option Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF (Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat)) :=
  match output with
  | none => PMF.pure (lazyOnlineNullResult memory input [] oracle)
  | some point => lazyOnlineValidResult memory input point oracle

attribute [local irreducible] onlineSamplingBudget onlinePrefixCost onlineSampling

private theorem onlineFuel_bound (parsed sampled : Nat)
    (parsedBound : parsed ≤ 20695) (sampledBound : sampled ≤ 120738687) :
    parsed + 3 + (1 + (sampled + 1678841 + 84355 + (117 * 278638 + 200672))) ≤ 2 ^ 46 := by
  omega

/-- Every online request fits the same fixed fuel allowance. -/
theorem lazyOnlineMachine_run [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Option Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (wire : memory.bits 0 = GarbledCircuit.SimulatorProtocol.affine input ++
      GarbledCircuit.SimulatorProtocol.output output) :
    lazyOnlineMachine.run (2 ^ 46) ⟨0, memory⟩ oracle =
      (lazyOnlineResult memory input output oracle).map
        (Option.map fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2)) := by
  have prefixBound : onlinePrefixCost output ≤ 20695 := by
    have inputBound := onlineInput_budget output
    change 98 + onlineInputCost output ≤ 7273 at inputBound
    unfold onlinePrefixCost
    omega
  have sampled : onlineSamplingBudget 256 ≤ 120738687 :=
    le_trans (Nat.le_add_right _ 1)
      (le_trans (Nat.le_add_right _ (onlineSampling 256).size)
        (le_trans (Nat.le_add_right _ 1) onlineSampling_256_cost))
  cases output with
  | none =>
    have budget : onlinePrefixCost none + (117 * 1270 + 200672) ≤ 2 ^ 46 := by omega
    have execution := lazyOnlineMachine_null
      (2 ^ 46 - (onlinePrefixCost none + (117 * 1270 + 200672))) memory input [] oracle (by simpa using wire)
    rw [Nat.add_sub_of_le budget] at execution
    simpa only [lazyOnlineResult, PMF.pure_map] using execution
  | some point =>
    have budget : onlinePrefixCost (some point) + 3 +
        (1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672))) ≤ 2 ^ 46 :=
      onlineFuel_bound _ _ prefixBound sampled
    have execution := lazyOnlineMachine_valid
      (2 ^ 46 - (onlinePrefixCost (some point) + 3 +
        (1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672))))) memory input point oracle wire
    rw [Nat.add_sub_of_le budget] at execution
    exact execution

end
end Kriterion.ArgoMAC.ArithmeticSimulator
