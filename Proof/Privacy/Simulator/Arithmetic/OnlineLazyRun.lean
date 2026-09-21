import Proof.Privacy.Simulator.Arithmetic.OnlineMachineInputFrame
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyPrepare
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingWitness
import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrefix
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineBranch
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish
import Proof.Privacy.Simulator.Arithmetic.GateTypedData
import Proof.Privacy.Simulator.Arithmetic.GateLoopBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine
noncomputable section
set_option maxRecDepth 8192
attribute [local irreducible] curveGatePlan pointGatePlan onlineMachineCode lazyGateLoopResults

/-- The curve setup installs its three private pointers. -/
theorem lazyOnlineMachine_curveSetup_run [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (3 + fuel) ⟨1435659, memory⟩ oracle =
      (lazyOnlineMachine.run fuel ⟨1435662, executeLinear onlineOriginalSetup memory⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  apply Simulator.run_prefix lazyOnlineMachine 3 fuel _ _ oracle
  exact linear_continue lazyOnlineMachine.arithmetic onlineOriginalSetup
    (onlineBodyLabels 1435659 3 (by decide) 1435662)
    (lazyOnlineMachine_linear _ _ (onlineMachine_curveSetup 256) (by
      intro index inside
      have bound : index < 3 := inside
      rw [onlineBodyLabels_active _ _ _ _ _ bound]
      exact ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩)) memory fuel

/-- The point setup installs its three private pointers. -/
theorem lazyOnlineMachine_pointSetup_run [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (3 + fuel) ⟨2751385, memory⟩ oracle =
      (lazyOnlineMachine.run fuel ⟨2751388, executeLinear onlinePointSetup memory⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  apply Simulator.run_prefix lazyOnlineMachine 3 fuel _ _ oracle
  exact linear_continue lazyOnlineMachine.arithmetic onlinePointSetup
    (onlineBodyLabels 2751385 3 (by decide) 2751388)
    (lazyOnlineMachine_linear _ _ (onlineMachine_pointSetup 256) (by
      intro index inside
      have bound : index < 3 := inside
      rw [onlineBodyLabels_active _ _ _ _ _ bound]
      exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inl (by omega)⟩)) memory fuel

/-- The absent-output suffix tests its tag and writes the final labels. -/
theorem lazyOnlineMachine_nullFinish [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (absent : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    lazyOnlineMachine.run (200666 + fuel) ⟨2751382, memory⟩ oracle =
      PMF.pure (some (⟨290305298, onlineFinalMemory (onlineTagMemory memory)⟩, oracle, 200666)) := by
  rw [show 200666 + fuel = 3 + (200663 + fuel) by omega,
    lazyOnlineMachine_secondBranch_continue]
  simp only [onlineBranchReturn, absent, if_true]
  rw [lazyOnlineMachine_finish, PMF.pure_map]
  rfl

/-- The curve loop aborts only when the fixed oracle refuses a program. -/
theorem lazyOnlineMachine_nullGates [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (absent : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    lazyOnlineMachine.run (117 * 1270 + 200666 + fuel) ⟨1435662, memory⟩ oracle =
      match lazyGateLoopResults curveGatePlan 1270 0 memory oracle with
      | none => PMF.pure none
      | some result => PMF.pure (some
          (⟨290305298, onlineFinalMemory (onlineTagMemory result.1)⟩, result.2.1, result.2.2 + 200666)) := by
  have continued := lazyGateLoopBlock_continue lazyOnlineMachine curveGatePlan
    (fun pc => onlineBranchLabels 1435662 1315720 (by decide) 2751382 pc.val)
    lazyOnlineMachine_curveGates 1270 0 (200666 + fuel) memory oracle (by decide)
  change lazyOnlineMachine.run (117 * 1270 + (200666 + fuel)) ⟨1435662, memory⟩ oracle = _ at continued
  rw [Nat.add_assoc, continued]
  cases reached : lazyGateLoopResults curveGatePlan 1270 0 memory oracle with
  | none => rfl
  | some result =>
    have bound := lazyGateLoopResults_cost curveGatePlan 1270 0 memory oracle result reached
    have agreement := GatePrivateAgreement.afterLazyLoop curveGatePlan 1270 0 memory memory oracle
      (GatePrivateAgreement.refl memory) result reached
    have retained : result.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0 :=
      (agreement.words (onlineInputBase + 2) (by decide) (by decide)).trans absent
    change (lazyOnlineMachine.run (117 * 1270 + (200666 + fuel) - result.2.2)
      ⟨2751382, result.1⟩ result.2.1).map _ = _
    rw [show 117 * 1270 + (200666 + fuel) - result.2.2 =
      200666 + (117 * 1270 + fuel - result.2.2) by omega,
      lazyOnlineMachine_nullFinish _ result.1 result.2.1 retained, PMF.pure_map]
    simp only [Option.map_some, Nat.add_comm]

private theorem loopFinish [BN254.FieldCertificate] {count : Nat}
    (host : Simulator) (plan : Vector GateCode count)
    (labels : Fin (1036 * count + 2) → Fin (host.size + 1))
    (present : ContainsLazyGateLoop host plan labels)
    (start stop final : Fin (host.size + 1))
    (entry : labels (gateLoopBoundary 0 (by omega)) = start)
    (returned : labels (gateLoopBoundary count (by omega)) = stop)
    (suffix fuel : Nat) (finish : Memory → Memory)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (continued : ∀ memory (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) fuel,
      host.run (suffix + fuel) ⟨stop, memory⟩ oracle =
        PMF.pure (some (⟨final, finish memory⟩, oracle, suffix))) :
    host.run (117 * count + suffix + fuel) ⟨start, memory⟩ oracle =
      match lazyGateLoopResults plan count 0 memory oracle with
      | none => PMF.pure none
      | some result => PMF.pure (some (⟨final, finish result.1⟩, result.2.1, result.2.2 + suffix)) := by
  have executed := lazyGateLoopBlock_continue host plan labels present count 0
    (suffix + fuel) memory oracle (by omega)
  simp only [entry, Nat.zero_add, returned] at executed
  rw [Nat.add_assoc, executed]
  cases reached : lazyGateLoopResults plan count 0 memory oracle with
  | none => rfl
  | some result =>
    have bound := lazyGateLoopResults_cost plan count 0 memory oracle result reached
    change (host.run (117 * count + (suffix + fuel) - result.2.2)
      ⟨stop, result.1⟩ result.2.1).map _ = _
    rw [show 117 * count + (suffix + fuel) - result.2.2 =
      suffix + (117 * count + fuel - result.2.2) by omega, continued, PMF.pure_map]
    simp only [Option.map_some, Nat.add_comm]

/-- The point loop writes the final labels after its last accepted program. -/
theorem lazyOnlineMachine_pointGates_finish [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (117 * 277368 + 200663 + fuel) ⟨2751388, memory⟩ oracle =
      match lazyGateLoopResults pointGatePlan 277368 0 memory oracle with
      | none => PMF.pure none
      | some result => PMF.pure (some
          (⟨290305298, onlineFinalMemory result.1⟩, result.2.1, result.2.2 + 200663)) := by
  exact loopFinish lazyOnlineMachine pointGatePlan
    (fun pc => onlineBranchLabels 2751388 287353248 (by decide) 290104636 pc.val)
    lazyOnlineMachine_pointGates 2751388 290104636 290305298 (by decide) (by decide)
    200663 fuel onlineFinalMemory memory oracle
    (fun memory oracle fuel => lazyOnlineMachine_finish fuel memory oracle)

private theorem pointBranchWith [BN254.FieldCertificate]
    (source : Memory → LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex →
      Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat))
    (pointRun : ∀ fuel memory oracle,
      lazyOnlineMachine.run (117 * 277368 + 200663 + fuel) ⟨2751388, memory⟩ oracle =
        match source memory oracle with
        | none => PMF.pure none
        | some result => PMF.pure (some (⟨290305298, onlineFinalMemory result.1⟩, result.2.1, result.2.2 + 200663)))
    (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (117 * 277368 + 200669 + fuel) ⟨2751382, memory⟩ oracle =
      match source (executeLinear onlinePointSetup (onlineTagMemory memory)) oracle with
      | none => PMF.pure none
      | some result => PMF.pure (some
          (⟨290305298, onlineFinalMemory result.1⟩, result.2.1, result.2.2 + 200669)) := by
  rw [show 117 * 277368 + 200669 + fuel = 3 + (3 + (117 * 277368 + 200663 + fuel)) by omega,
    lazyOnlineMachine_secondBranch_continue]
  simp only [onlineBranchReturn, if_neg present]
  rw [lazyOnlineMachine_pointSetup_run, pointRun]
  cases source (executeLinear onlinePointSetup (onlineTagMemory memory)) oracle <;>
    simp [PMF.pure_map, Nat.add_assoc]

/-- The present-output suffix selects the point loop and its final labels. -/
theorem lazyOnlineMachine_pointBranch [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (117 * 277368 + 200669 + fuel) ⟨2751382, memory⟩ oracle =
      match lazyGateLoopResults pointGatePlan 277368 0
        (executeLinear onlinePointSetup (onlineTagMemory memory)) oracle with
      | none => PMF.pure none
      | some result => PMF.pure (some
          (⟨290305298, onlineFinalMemory result.1⟩, result.2.1, result.2.2 + 200669)) := by
  exact pointBranchWith (lazyGateLoopResults pointGatePlan 277368 0)
    lazyOnlineMachine_pointGates_finish fuel memory oracle present

/-- The two gate loops share the fixed oracle and the private linked-label buffer. -/
def lazyOnlineValidGateResult (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat) := do
  let curve ← lazyGateLoopResults curveGatePlan 1270 0 (executeLinear onlineOriginalSetup memory) oracle
  let point ← lazyGateLoopResults pointGatePlan 277368 0
    (executeLinear onlinePointSetup (onlineTagMemory curve.1)) curve.2.1
  pure (onlineFinalMemory point.1, point.2.1, curve.2.2 + point.2.2 + 200672)

private theorem validGatesWith [BN254.FieldCertificate]
    (source : Memory → LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex →
      Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat))
    (pointRun : ∀ fuel memory oracle,
      memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 →
      lazyOnlineMachine.run (117 * 277368 + 200669 + fuel) ⟨2751382, memory⟩ oracle =
        match source (executeLinear onlinePointSetup (onlineTagMemory memory)) oracle with
        | none => PMF.pure none
        | some result => PMF.pure (some (⟨290305298, onlineFinalMemory result.1⟩, result.2.1, result.2.2 + 200669)))
    (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (117 * 278638 + 200672 + fuel) ⟨1435659, memory⟩ oracle =
      PMF.pure ((do
        let curve ← lazyGateLoopResults curveGatePlan 1270 0 (executeLinear onlineOriginalSetup memory) oracle
        let point ← source (executeLinear onlinePointSetup (onlineTagMemory curve.1)) curve.2.1
        pure (onlineFinalMemory point.1, point.2.1, curve.2.2 + point.2.2 + 200672)).map
        (fun result : Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat =>
          (⟨290305298, result.1⟩, result.2.1, result.2.2))) := by
  let initial := executeLinear onlineOriginalSetup memory
  rw [show 117 * 278638 + 200672 + fuel =
    3 + (117 * 1270 + (117 * 277368 + 200669 + fuel)) by omega,
    lazyOnlineMachine_curveSetup_run]
  have continued := lazyGateLoopBlock_continue lazyOnlineMachine curveGatePlan
    (fun pc => onlineBranchLabels 1435662 1315720 (by decide) 2751382 pc.val)
    lazyOnlineMachine_curveGates 1270 0 (117 * 277368 + 200669 + fuel) initial oracle (by decide)
  change lazyOnlineMachine.run (117 * 1270 + (117 * 277368 + 200669 + fuel)) ⟨1435662, initial⟩ oracle = _ at continued
  rw [continued]
  dsimp only [Bind.bind]
  cases reached : lazyGateLoopResults curveGatePlan 1270 0 initial oracle with
  | none => simp [PMF.pure_map]
  | some curve =>
    have bound := lazyGateLoopResults_cost curveGatePlan 1270 0 initial oracle curve reached
    have agreement := GatePrivateAgreement.afterLazyLoop curveGatePlan 1270 0 initial initial oracle
      (GatePrivateAgreement.refl initial) curve reached
    have retained : curve.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 := by
      rw [agreement.words (onlineInputBase + 2) (by decide) (by decide)]
      exact present
    simp only [Option.bind_some]
    change ((lazyOnlineMachine.run (117 * 1270 + (117 * 277368 + 200669 + fuel) - curve.2.2)
      ⟨2751382, curve.1⟩ curve.2.1).map _).map _ = _
    rw [show 117 * 1270 + (117 * 277368 + 200669 + fuel) - curve.2.2 =
      117 * 277368 + 200669 + (117 * 1270 + fuel - curve.2.2) by omega,
      pointRun _ curve.1 curve.2.1 retained]
    cases source (executeLinear onlinePointSetup (onlineTagMemory curve.1)) curve.2.1 <;>
      simp [PMF.pure_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The present-output gate phase has a fixed budget for both loops. -/
theorem lazyOnlineMachine_validGates [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (117 * 278638 + 200672 + fuel) ⟨1435659, memory⟩ oracle =
      PMF.pure ((lazyOnlineValidGateResult memory oracle).map
        (fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2))) := by
  exact validGatesWith (lazyGateLoopResults pointGatePlan 277368 0)
    lazyOnlineMachine_pointBranch fuel memory oracle present

/-- The absent-output source contains one strict curve loop. -/
def lazyOnlineNullResult [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (rest : List Bool) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat) :=
  (lazyGateLoopResults curveGatePlan 1270 0
    (executeLinear onlineOriginalSetup (onlineTagMemory (onlineCurveMemory memory input none rest))) oracle).map
    (fun result => (onlineFinalMemory (onlineTagMemory result.1), result.2.1,
      result.2.2 + onlinePrefixCost none + 200672))

/-- The absent-output execution uses only the curve loop and a constant private prefix. -/
theorem lazyOnlineMachine_null [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (input : BN254.AffineInput) (rest : List Bool)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (wire : memory.bits 0 = GarbledCircuit.SimulatorProtocol.affine input ++
      GarbledCircuit.SimulatorProtocol.output none ++ rest) :
    lazyOnlineMachine.run (onlinePrefixCost none + (117 * 1270 + 200672) + fuel) ⟨0, memory⟩ oracle =
      PMF.pure ((lazyOnlineNullResult memory input rest oracle).map
        (fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2))) := by
  have absent : (onlineCurveMemory memory input none rest).ram
      (BitVec.ofNat 256 (onlineInputBase + 2)) = 0 := by
    rw [onlineCurveMemory_tag]
    rfl
  rw [show onlinePrefixCost none + (117 * 1270 + 200672) + fuel =
    onlinePrefixCost none + (3 + (3 + (117 * 1270 + 200666 + fuel))) by omega,
    lazyOnlineMachine_prefix_run memory input none rest wire,
    lazyOnlineMachine_firstBranch_continue]
  simp only [onlineBranchReturn, absent, if_true]
  rw [lazyOnlineMachine_curveSetup_run, lazyOnlineMachine_nullGates _ _ _ (show
    (executeLinear onlineOriginalSetup (onlineTagMemory (onlineCurveMemory memory input none rest))).ram
      (BitVec.ofNat 256 (onlineInputBase + 2)) = 0 from absent)]
  unfold lazyOnlineNullResult
  cases lazyGateLoopResults curveGatePlan 1270 0
    (executeLinear onlineOriginalSetup (onlineTagMemory (onlineCurveMemory memory input none rest))) oracle <;>
    simp [PMF.pure_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine
noncomputable section
set_option maxRecDepth 4096
attribute [local irreducible] lazyGateLoopResults lazyOnlineValidGateResult

/-- The link enters both gate loops after it completes its fixed query schedule. -/
theorem lazyOnlineMachine_linked [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (ready : ∀ linked ∈ (lazyEncLinkSamples memory oracle).support,
      linked.1.2.2 = 7466 ∧ linked.1.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (84355 + (117 * 278638 + 200672) + fuel) ⟨1428193, memory⟩ oracle =
      (lazyEncLinkSamples memory oracle).bind (fun linked => PMF.pure
        ((lazyOnlineValidGateResult linked.1.1 linked.2).map
          (fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2 + linked.1.2.1)))) := by
  have continued := simulator_encLink_samples lazyOnlineMachine
    (fun pc => onlineBranchLabels 1428193 7466 (by decide) 1435659 pc.val)
    lazyOnlineMachine_link memory oracle (117 * 278638 + 200672 + fuel)
  change lazyOnlineMachine.run (84355 + (117 * 278638 + 200672 + fuel)) ⟨1428193, memory⟩ oracle = _ at continued
  rw [Nat.add_assoc, continued]
  apply PMF.bind_congr
  intro linked supported
  have facts := ready linked supported
  have bound := lazyEncLinkSamples_cost memory oracle linked supported
  rw [facts.1]
  change (lazyOnlineMachine.run (84355 + (117 * 278638 + 200672 + fuel) - linked.1.2.1)
    ⟨1435659, linked.1.1⟩ linked.2).map _ = _
  rw [show 84355 + (117 * 278638 + 200672 + fuel) - linked.1.2.1 =
    117 * 278638 + 200672 + (84355 + fuel - linked.1.2.1) by omega,
    lazyOnlineMachine_validGates _ linked.1.1 linked.2 facts.2, PMF.pure_map]
  simp only [Option.map_map, Function.comp_def]

/-- The valid body uses the finite private sampler and the fixed oracle. -/
def lazyOnlineValidBodyResult [BN254.FieldCertificate] [BN254.GroupCertificate]
    (memory : Memory) (output : BN254.Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF (Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat)) :=
  let initial := executeLinear onlineSampleSetup memory
  (onlineSamplingMemory 256 initial).bind fun sampled =>
    let coin := onlineSamplingCoin 256 initial sampled
    (lazyEncLinkSamples (onlinePreparedMemory sampled.1 output coin) oracle).bind fun linked =>
      PMF.pure ((lazyOnlineValidGateResult linked.1.1 linked.2).map fun result =>
        (result.1, result.2.1, result.2.2 + linked.1.2.1 + onlinePrepareCost coin + sampled.2 + 1))

/-- The valid body charges every private and oracle instruction. -/
theorem lazyOnlineMachine_validBody [BN254.FieldCertificate] [BN254.GroupCertificate]
    (fuel : Nat) (memory : Memory) (output : BN254.Point)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (selected : ∀ sampled ∈ (onlineSamplingMemory 256 (executeLinear onlineSampleSetup memory)).support,
      selectedOutputPoint sampled.1.ram (BitVec.ofNat 256 onlineInputBase) = some output)
    (ready : ∀ sampled ∈ (onlineSamplingMemory 256 (executeLinear onlineSampleSetup memory)).support,
      ∀ linked ∈ (lazyEncLinkSamples (onlinePreparedMemory sampled.1 output
        (onlineSamplingCoin 256 (executeLinear onlineSampleSetup memory) sampled)) oracle).support,
        linked.1.2.2 = 7466 ∧ linked.1.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0) :
    lazyOnlineMachine.run (1 + (onlineSamplingBudget 256 + 1678841 + 84355 +
      (117 * 278638 + 200672)) + fuel) ⟨13621, memory⟩ oracle =
      (lazyOnlineValidBodyResult memory output oracle).map
        (Option.map fun result => (⟨290305298, result.1⟩, result.2.1, result.2.2)) := by
  let initial := executeLinear onlineSampleSetup memory
  have setup : ∀ reserve, lazyOnlineMachine.run (1 + reserve) ⟨13621, memory⟩ oracle =
      (lazyOnlineMachine.run reserve ⟨13622, initial⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
    intro reserve
    apply Simulator.run_prefix lazyOnlineMachine 1 reserve _ _ oracle
    exact linear_continue lazyOnlineMachine.arithmetic onlineSampleSetup
      (onlineBodyLabels 13621 1 (by decide) 13622)
      (lazyOnlineMachine_linearBefore _ _ _ _ _ (onlineMachine_sampleSetup 256) (by decide) (by decide)) memory reserve
  rw [show 1 + (onlineSamplingBudget 256 + 1678841 + 84355 + (117 * 278638 + 200672)) + fuel =
    1 + (onlineSamplingBudget 256 + (1678841 + 84355 + (117 * 278638 + 200672) + fuel)) by omega,
    setup, lazyOnlineMachine_sampling_run, PMF.map_bind]
  unfold lazyOnlineValidBodyResult
  simp only [PMF.map_bind]
  apply PMF.bind_congr
  intro sampled supported
  let coin := onlineSamplingCoin 256 initial sampled
  have sampleBound := onlineSamplingMemory_cost 256 initial sampled.1 sampled.2 supported
  have prepareBound := onlinePrepareCost_bound coin
  have words := onlineSamplingCoin_words 256 initial sampled supported
  change WordsAt sampled.1.ram (BitVec.ofNat 256 onlineSampleBase) 0 (onlineWords coin) at words
  have rest : onlineSamplingBudget 256 + (1678841 + 84355 + (117 * 278638 + 200672) + fuel) - sampled.2 =
      onlinePrepareCost coin + (84355 + (117 * 278638 + 200672) +
        (onlineSamplingBudget 256 + 1678841 + fuel - sampled.2 - onlinePrepareCost coin)) := by omega
  rw [rest, lazyOnlineMachine_prepare_run sampled.1 output coin words (selected sampled supported),
    lazyOnlineMachine_linked _ _ oracle (ready sampled supported), PMF.map_bind, PMF.map_bind, PMF.map_bind]
  apply PMF.bind_congr
  intro linked member
  simp [PMF.pure_map, Option.map_map, Function.comp_def, coin, initial, Nat.add_assoc]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
