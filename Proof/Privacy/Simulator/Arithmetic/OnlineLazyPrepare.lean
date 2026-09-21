import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrepare
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The actual private preparation returns its exact memory to the public link phase. -/
theorem lazyOnlineMachine_prepare [BN254.FieldCertificate] [BN254.GroupCertificate]
    (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (stored : WordsAt memory.ram (BitVec.ofNat 256 onlineSampleBase) 0 (onlineWords sample))
    (selected : selectedOutputPoint memory.ram (BitVec.ofNat 256 onlineInputBase) = some output) :
    FixedContinuation lazyOnlineMachine.arithmetic 22393 1428193 memory
      (onlinePreparedMemory memory output sample) (onlinePrepareCost sample) := by
  have targetSetupCode := lazyOnlineMachine_linearBefore onlineTargetSetup 22393 4 22397 (by decide)
    (onlineMachine_targetSetup 256) (by decide) (by decide)
  have retargetSetupCode := lazyOnlineMachine_linearBefore onlineRetargetSetup 26685 3 26688 (by decide)
    (onlineMachine_retargetSetup 256) (by decide) (by decide)
  have pointRetargetCode := lazyOnlineMachine_linearBefore retargetPointCode 26688 1401497 1428185 (by decide)
    (onlineMachine_pointRetarget 256) (by decide) (by decide)
  have linkSetupCode := lazyOnlineMachine_linear onlineLinkSetup
    (onlineBodyLabels 1428185 8 (by decide) 1428193) (onlineMachine_linkSetup 256) (by
      intro index inside
      have bound : index < 8 := inside
      rw [onlineBodyLabels_active _ _ _ _ _ bound]
      exact ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩)
  let targetInitial := executeLinear onlineTargetSetup memory
  let retargetInitial := executeLinear onlineRetargetSetup (onlineTargetMemory memory output sample)
  let retargeted := executeLinear retargetPointCode retargetInitial
  have setup := onlineTargetSetup_state memory
  have first : FixedContinuation lazyOnlineMachine.arithmetic 22393 22397 memory targetInitial 4 := by
    intro fuel
    exact linear_continue lazyOnlineMachine.arithmetic onlineTargetSetup
      (onlineBodyLabels 22393 4 (by decide) 22397) targetSetupCode memory fuel
  have targets : FixedContinuation lazyOnlineMachine.arithmetic 22397 26685 targetInitial
      (onlineTargetMemory memory output sample) (outputTargetsCost sample.1) := by
    intro fuel
    have words : WordsAt targetInitial.ram (targetInitial.registers 14) 0 (onlineWords sample) := by
      rw [show targetInitial.ram = memory.ram from setup.1,
        show targetInitial.registers 14 = BitVec.ofNat 256 onlineSampleBase from setup.2.2.2.2.1]
      exact stored
    have outputWord : selectedOutputPoint targetInitial.ram (targetInitial.registers 11) = some output := by
      rw [show targetInitial.ram = memory.ram from setup.1,
        show targetInitial.registers 11 = BitVec.ofNat 256 onlineInputBase from setup.2.2.2.1]
      exact selected
    have law := outputTargetsBlock_run lazyOnlineMachine.arithmetic
      (fun pc => onlineBodyLabels 22397 4288 (by decide) 26685 pc.val) lazyOnlineMachine_targets
      fuel targetInitial output sample (onlineTargetSetup_pointer memory) words outputWord (onlineTargetSetup_separate memory)
    rw [Nat.add_comm fuel (outputTargetsCost sample.1)] at law
    exact law
  have pointSetup : FixedContinuation lazyOnlineMachine.arithmetic 26685 26688
      (onlineTargetMemory memory output sample) retargetInitial 3 := by
    intro fuel
    exact linear_continue lazyOnlineMachine.arithmetic onlineRetargetSetup
      (onlineBodyLabels 26685 3 (by decide) 26688) retargetSetupCode
      (onlineTargetMemory memory output sample) fuel
  have pointRun : FixedContinuation lazyOnlineMachine.arithmetic 26688 1428185 retargetInitial retargeted 1401497 := by
    intro fuel
    exact retargetPointHost_continue lazyOnlineMachine.arithmetic
      (onlineBodyLabels 26688 1401497 (by decide) 1428185) pointRetargetCode retargetInitial fuel
  have linkSetup : FixedContinuation lazyOnlineMachine.arithmetic 1428185 1428193 retargeted
      (onlinePreparedMemory memory output sample) 8 := by
    intro fuel
    exact linear_continue lazyOnlineMachine.arithmetic onlineLinkSetup
      (onlineBodyLabels 1428185 8 (by decide) 1428193) linkSetupCode retargeted fuel
  exact first.trans _ _ _ _ _ _ _ _ _
    (targets.trans _ _ _ _ _ _ _ _ _ (pointSetup.trans _ _ _ _ _ _ _ _ _
      (pointRun.trans _ _ _ _ _ _ _ _ _ linkSetup)))

/-- The fixed-oracle machine preserves L during all private preparation steps. -/
theorem lazyOnlineMachine_prepare_run [BN254.FieldCertificate] [BN254.GroupCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (stored : WordsAt memory.ram (BitVec.ofNat 256 onlineSampleBase) 0 (onlineWords sample))
    (selected : selectedOutputPoint memory.ram (BitVec.ofNat 256 onlineInputBase) = some output)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    lazyOnlineMachine.run (onlinePrepareCost sample + fuel) ⟨22393, memory⟩ oracle =
      (lazyOnlineMachine.run fuel ⟨1428193, onlinePreparedMemory memory output sample⟩ oracle).map
        (Option.map fun final => (final.1, final.2.1, final.2.2 + onlinePrepareCost sample)) := by
  exact lazyOnlineMachine.run_prefix _ _ _ _ oracle
    (lazyOnlineMachine_prepare memory output sample stored selected fuel)

/-- The private sampler preserves L and charges every sample instruction. -/
theorem lazyOnlineMachine_sampling_run [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    lazyOnlineMachine.run (onlineSamplingBudget 256 + fuel) ⟨13622, memory⟩ oracle =
      (onlineSamplingMemory 256 memory).bind fun sample =>
        (lazyOnlineMachine.run (onlineSamplingBudget 256 + fuel - sample.2) ⟨22393, sample.1⟩ oracle).map
          (Option.map fun final => (final.1, final.2.1, final.2.2 + sample.2)) := by
  have sampled := onlineSamplingBlock_run lazyOnlineMachine.arithmetic 256
    (fun pc => onlineBodyLabels 13622 8771 (by decide) 22393 pc.val)
    lazyOnlineMachine_samples fuel memory (by decide)
  change run lazyOnlineMachine.arithmetic (onlineSamplingBudget 256 + fuel) ⟨13622, memory⟩ =
    (onlineSamplingMemory 256 memory).bind (fun sample =>
      (run lazyOnlineMachine.arithmetic (onlineSamplingBudget 256 + fuel - sample.2)
        ⟨22393, sample.1⟩).map (Option.map fun final => (final.1, final.2 + sample.2))) at sampled
  rw [lazyOnlineMachine.run_arithmetic_prefix, sampled, PMF.bind_bind]
  apply PMF.bind_congr
  intro sample supported
  have bound := onlineSamplingMemory_cost 256 memory sample.1 sample.2 supported
  rw [PMF.bind_map, lazyOnlineMachine.run_arithmetic_prefix, PMF.map_bind]
  apply PMF.bind_congr
  intro outcome member
  cases outcome with
  | none => simp [PMF.pure_map]
  | some outcome =>
    rcases outcome with ⟨next, cost⟩
    have positive := run_positive lazyOnlineMachine.arithmetic
      (onlineSamplingBudget 256 + fuel - sample.2) ⟨22393, sample.1⟩ next cost member
    have remaining : onlineSamplingBudget 256 + fuel - (cost + sample.2) + 1 =
        onlineSamplingBudget 256 + fuel - sample.2 - cost + 1 := by omega
    simp only [Function.comp_apply, Option.map_some, remaining, PMF.map_comp]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some result =>
      simp only [Function.comp_apply, Option.map_some]
      congr 3
      omega

end Kriterion.ArgoMAC.ArithmeticSimulator
