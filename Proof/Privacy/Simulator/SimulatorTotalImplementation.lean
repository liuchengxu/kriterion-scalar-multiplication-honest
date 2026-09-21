import Proof.Privacy.Simulator.SimulatorTotalPhaseCost
import Proof.Privacy.Simulator.SimulatorExternalBits
import Proof.Privacy.Simulator.SimulatorImplementation
import Proof.Privacy.Simulator.SimulatorTotalSampling
import Proof.Privacy.Simulator.SimulatorTotalLaw

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling SimulatorScheduleCost
namespace SimulatorMachine.TotalImplementation
open Implementation

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
attribute [local irreducible] SimulatorRejectionCost.PositiveWidths

/-- The total setup constructs each sampled array, private cache, and public table once. -/
def setupCode : Code ((PrivateCache × Pipeline.Table) × Nat) 838208 :=
  SimulatorSamplingCost.offlineWithCost.map fun sampled =>
    let prepared := readyWithCost sampled.1
    (prepared.1, sampled.2 + prepared.2)

/-- The setup returns its complete state after every finite draw sequence. -/
def setup (attempts : Nat) : BitCode ((PrivateCache × Pipeline.Table) × Nat) :=
  setupCode.total attempts

theorem setupCode_law : setupCode.law.map Prod.fst = offlineReady.law := by
  simp only [setupCode, Code.map_law, PMF.map_comp, Function.comp_def, readyWithCost_value]
  change SimulatorSamplingCost.offlineWithCost.law.map (ready ∘ Prod.fst) = _
  rw [← PMF.map_comp, SimulatorSamplingCost.offline_law]
  rfl

theorem setupCode_bound : SimulatorSamplingCost.Bounded setupCode 2605005 := by
  intro Seed random seed
  have bound := SimulatorSamplingCost.offline_bound Seed random seed
  simp only [setupCode, Code.map_run, readyWithCost_count]
  omega

theorem setupCode_size : setupCode.DrawSizeLe (2 ^ 256) :=
  Code.map_drawSizeLe _ _ SimulatorSamplingCost.offline_size

/-- The setup charge also bounds tapes that use fallback values. -/
theorem setup_work {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    ((setup attempts).run random seed).1.1.2 ≤ 2605005 := by
  unfold setup
  rw [Code.total_run]
  exact setupCode_bound Seed (totalRandom random attempts) seed

theorem setup_bits {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    ((setup attempts).run random seed).2 ≤ 838208 * (257 * attempts) :=
  Code.total_bits random attempts setupCode setupCode_size seed

/-- This total encoder continues the sparse oracle after every fallback draw. -/
def encode [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) : BitCode ((Garbling.Labels × SparseState) × Nat) :=
  (SimulatorSamplingCost.onlineWithCost.total attempts).bind fun sample =>
    ((selected cache.coin cache.tables input output sample.1).total sparseDraw attempts state).bind fun result =>
      .pure ((result.1.1, result.2), sample.2 + result.1.2)

/-- The encoder returns a total label value and the updated sparse state. -/
def labels [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) : BitCode (Garbling.Labels × SparseState) :=
  (encode attempts cache input output state).bind fun result => .pure result.1

/-- The encoder charges the complete private sampler and the cached local program. -/
theorem encode_work [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) (seed : Seed) :
    ((encode attempts cache input output state).run random seed).1.1.2 ≤ 51183699 := by
  have sampled := SimulatorSamplingCost.online_bound Seed (totalRandom random attempts) seed
  have runSample := Code.total_run random attempts SimulatorSamplingCost.onlineWithCost seed
  simp only [encode, BitCode.bind_run, BitCode.run]
  have runProgram := Program.total_run sparseDraw random attempts
    (selected cache.coin cache.tables input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2
  have costSame := congrArg (fun result => result.1.2) runProgram
  simp only [Program.execute] at costSame
  rw [costSame]
  have localBound := selected_local_bound
    (randomHandler sparseDraw (totalRandom random attempts)) cache.coin cache.tables input output
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1
    (state, ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2)
  rw [← runSample] at sampled
  omega

/-- The total encoder has a strict fair-bit bound for all fallback paths. -/
theorem encode_bits [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) (seed : Seed) :
    ((encode attempts cache input output state).run random seed).2 ≤ 836604 * (257 * attempts) := by
  have first := Code.total_bits random attempts SimulatorSamplingCost.onlineWithCost
    SimulatorSamplingCost.online_size seed
  have second := Program.total_bits sparseDraw sparseDraw_sizeLe random attempts
    (selected cache.coin cache.tables input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2
  have budget : onlineBudget output ≤ 836423 := by cases output <;> simp [onlineBudget]
  have combined := Nat.add_le_add first (second.trans (Nat.mul_le_mul_right _ budget))
  simpa only [encode, BitCode.bind_run, BitCode.run, Nat.add_zero, ← Nat.add_mul] using combined

theorem labels_bits [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) (seed : Seed) :
    ((labels attempts cache input output state).run random seed).2 ≤ 836604 * (257 * attempts) := by
  simpa only [labels, BitCode.bind_run, BitCode.run, Nat.add_zero] using
    encode_bits random attempts cache input output state seed

/-- Every setup block has positive width. -/
theorem setup_positive (attempts : Nat) :
    SimulatorRejectionCost.PositiveWidths (setup attempts) := Code.total_positive attempts setupCode

/-- Every total label block has positive width. -/
theorem labels_positive [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) :
    SimulatorRejectionCost.PositiveWidths (labels attempts cache input output state) :=
  SimulatorRejectionCost.positive_bind _ _
    (SimulatorRejectionCost.positive_bind _ _
      (Code.total_positive attempts SimulatorSamplingCost.onlineWithCost)
      (fun sample => SimulatorRejectionCost.positive_bind _ _
        (Program.total_positive sparseDraw attempts
          (selected cache.coin cache.tables input output sample.1) state)
        (fun _ => by unfold SimulatorRejectionCost.PositiveWidths; trivial)))
    (fun _ => by unfold SimulatorRejectionCost.PositiveWidths; trivial)

/-- The total setup's rejection control uses at most four operations per fair bit. -/
theorem setup_control {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed) (attempts : Nat) (seed : Seed) :
    (SimulatorRejectionCost.runWithCost random (setup attempts) seed).2.2 ≤
      4 * ((setup attempts).run random seed).2 :=
  SimulatorRejectionCost.runWithCost_bound random _ (setup_positive attempts) seed

/-- The total encoder's rejection control uses the same per-bit allowance. -/
theorem labels_control [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) (seed : Seed) :
    (SimulatorRejectionCost.runWithCost random (labels attempts cache input output state) seed).2.2 ≤
      4 * ((labels attempts cache input output state).run random seed).2 :=
  SimulatorRejectionCost.runWithCost_bound random _ (labels_positive attempts cache input output state) seed

/-- Marking internal requests preserves each total finite execution. -/
theorem internal_total {A : Type} {budget : Nat}
    (program : Program spec A budget) (attempts : Nat) (state : SparseState) :
    program.internal.total combinedDraw attempts state = program.total sparseDraw attempts state := by
  induction program generalizing state with
  | pure => rfl
  | query request next ih =>
      simp only [Program.internal, Program.total, combinedDraw, ih]
  | map f source ih => simp only [Program.internal, Program.total, ih]
  | bind source next first second => simp only [Program.internal, Program.total, first, second]
  | weaken source bounded ih => exact ih state

/-- This program retains the local counter and uses one fixed private query budget. -/
def countedProgram [FieldCertificate] [GroupCertificate]
    (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (sample : SimulatorSamplingCost.OnlineCoin) : Program combinedSpec (Garbling.Labels × Nat) 836423 :=
  .weaken (selected cache.coin cache.tables input output sample).internal
    (by cases output <;> simp [onlineBudget])

theorem countedProgram_total [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (sample : SimulatorSamplingCost.OnlineCoin) (state : SparseState) :
    (countedProgram cache input output sample).total combinedDraw attempts state =
      (selected cache.coin cache.tables input output sample).total sparseDraw attempts state :=
  internal_total _ _ _

/-- This executor returns total labels, the next state, and both resource counters. -/
def execute [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    (Garbling.Labels × SparseState × Seed) × Nat × Nat × Nat :=
  let sampled := (SimulatorSamplingCost.onlineWithCost.total attempts).run random seed
  let result := Cost.executeTotalCost random attempts
    (countedProgram cache input output sampled.1.1.1) state sampled.1.2 depth
  ((result.1.1.1, result.1.2.1, result.1.2.2), result.2.1,
    sampled.1.1.2 + result.1.1.2 + result.2.2.1, sampled.2 + result.2.2.2)

/-- The runtime executes exactly the total label sampler used in the privacy game. -/
theorem execute_value [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    let result := (labels attempts cache input output state).run random seed
    (execute random attempts cache input output state seed depth).1 =
      (result.1.1.1, result.1.1.2, result.1.2) ∧
    (execute random attempts cache input output state seed depth).2.2.2 = result.2 := by
  have same := Cost.executeTotalCost_correct random attempts
    (countedProgram cache input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2 depth
  simp only [countedProgram_total] at same
  simp only [execute, labels, encode, BitCode.bind_run, BitCode.run, Nat.add_zero, same.1, same.2]
  trivial

/-- The complete local-work counter adds at most the checked encoder allowance. -/
theorem execute_local [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth : Nat) :
    let sampled := (SimulatorSamplingCost.onlineWithCost.total attempts).run random seed
    let result := Cost.executeTotalCost random attempts
      (countedProgram cache input output sampled.1.1.1) state sampled.1.2 depth
    (execute random attempts cache input output state seed depth).2.2.1 ≤ 51183699 + result.2.2.1 := by
  have same := Cost.executeTotalCost_correct random attempts
    (countedProgram cache input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2 depth
  simp only [countedProgram_total] at same
  have work := encode_work random attempts cache input output state seed
  simp only [encode, BitCode.bind_run, BitCode.run] at work
  have charged := congrArg (fun result => result.1.2) same.1
  dsimp only at charged
  rw [← charged] at work
  exact Nat.add_le_add_right work _

/-- The total runtime preserves the sparse bound and charges its complete private work. -/
theorem execute_resources [FieldCertificate] [GroupCertificate] {Seed : Type}
    (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput) (output : Option Point)
    (state : SparseState) (seed : Seed) (depth capacity : Nat)
    (bound : Cost.StateBound state capacity) (depthBound : depth ≤ capacity) :
    (execute random attempts cache input output state seed depth).2.1 ≤ 836423 ∧
    (execute random attempts cache input output state seed depth).2.2.1 ≤
      51183699 + 836423 * (10 * (capacity + 836423) + 16) ∧
    (execute random attempts cache input output state seed depth).2.2.2 ≤ 836604 * (257 * attempts) ∧
    Nonempty (Cost.StateBound (execute random attempts cache input output state seed depth).1.2.1
      (capacity + 836423)) := by
  have resources := Cost.executeTotalCost_resources random attempts
    (countedProgram cache input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2 depth capacity bound depthBound
  have same := Cost.executeTotalCost_correct random attempts
    (countedProgram cache input output
      ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.1.1) state
    ((SimulatorSamplingCost.onlineWithCost.total attempts).run random seed).1.2 depth
  simp only [countedProgram_total] at same
  have work := encode_work random attempts cache input output state seed
  simp only [encode, BitCode.bind_run, BitCode.run] at work
  have charged := congrArg (fun result => result.1.2) same.1
  dsimp only at charged
  rw [← charged] at work
  have bits := labels_bits random attempts cache input output state seed
  rw [← (execute_value random attempts cache input output state seed depth).2] at bits
  exact ⟨resources.1, Nat.add_le_add work resources.2.1, bits, resources.2.2⟩

noncomputable section

/-- The total setup retains the exact cached private-state distribution. -/
theorem setup_law (attempts : Nat) :
    TotalLaw attempts 838208 offlineReady.law ((setup attempts).law.map Prod.fst) := by
  rw [← setupCode_law]
  exact (Code.total_law attempts setupCode).map Prod.fst

/-- The total labels retain the complete sparse encoder's output distribution. -/
theorem labels_law [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (cache : PrivateCache) (input : AffineInput)
    (output : Option Point) (state : SparseState) :
    TotalLaw attempts 836604
      (runSampled sparseHandler (encoding cache.coin cache.tables input output) state)
      (labels attempts cache input output state).law := by
  have base := (Code.total_law attempts SimulatorSamplingCost.onlineWithCost).bind
    (fun sample => (Program.total_law sparseDraw attempts
      (selected cache.coin cache.tables input output sample.1) state).map
        (fun result => (result.1.1, result.2)))
  have budget : 181 + onlineBudget output ≤ 836604 := by cases output <;> simp [onlineBudget]
  have law := base.weaken budget
  have reference : SimulatorSamplingCost.onlineWithCost.law.bind
      (fun sample => ((selected cache.coin cache.tables input output sample.1).sampledLaw sparseDraw state).map
        (fun result => (result.1.1, result.2))) =
      runSampled sparseHandler (encoding cache.coin cache.tables input output) state := by
    rw [encoding, runSampled, ← SimulatorSamplingCost.online_law, PMF.bind_map]
    apply congrArg (PMF.bind SimulatorSamplingCost.onlineWithCost.law)
    funext sample
    exact (Program.sampledLaw_toOracle sparseDraw
      ((selected cache.coin cache.tables input output sample.1).map Prod.fst) state).symm
  rw [reference] at law
  simpa only [labels, encode, BitCode.bind_law, BitCode.law, PMF.bind_bind,
    PMF.pure_bind, PMF.map, Function.comp_def] using law

/-- Each external phase executes one total sparse-and-bit resource interpreter. -/
def external {A : Type} {budget : Nat} (attempts : Nat)
    (program : OracleProgram Garbling.oracleSpec A budget) (state : SparseState) (depth : Nat) :
    PMF (A × SparseState) :=
  (ExternalBits.runTotalWithResources attempts program state depth).map Prod.fst

/-- Every phase continues with total labels and a consistent sparse oracle state. -/
def continuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table)
    (state : SparseState) : PMF Bool :=
  (external attempts (adversary.prepare parameter auxiliary) state 0).bind fun prepared =>
    (external attempts (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2
      (adversary.preQueryBudget parameter)).bind fun selectedInput =>
      (labels attempts cache selectedInput.1.1
        ((Garbling.garbledCircuit construction).function scalar selectedInput.1.1) selectedInput.2).law.bind
        fun encoded => (external attempts
          (adversary.decide parameter table encoded.1 auxiliary selectedInput.1.2) encoded.2
          (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter + 836423)).map Prod.fst

/-- The complete three-phase continuation retains the exact simulator's common mass. -/
theorem continuation_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table)
    (state : SparseState) :
    TotalLaw attempts
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 836604)
      (Implementation.continuation adversary parameter scalar auxiliary cache table state)
      (continuation attempts adversary parameter scalar auxiliary cache table state) := by
  have law := (ExternalBits.runTotalWithResources_totalLaw attempts
    (adversary.prepare parameter auxiliary) state 0).bind fun prepared =>
      (ExternalBits.runTotalWithResources_totalLaw attempts
        (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2
        (adversary.preQueryBudget parameter)).bind fun selectedInput =>
        (labels_law attempts cache selectedInput.1.1
          ((Garbling.garbledCircuit construction).function scalar selectedInput.1.1) selectedInput.2).bind
          fun encoded => (ExternalBits.runTotalWithResources_totalLaw attempts
            (adversary.decide parameter table encoded.1 auxiliary selectedInput.1.2) encoded.2
            (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter + 836423)).map Prod.fst
  simpa only [Implementation.continuation, continuation, external,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using law

/-- The total game uses finite fair-bit samplers and always lets the adversary decide. -/
def game [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (setup attempts).law.bind fun prepared =>
    continuation attempts adversary parameter scalar auxiliary prepared.1.1 prepared.1.2 (initial initialMetadata)

/-- The total finite game retains the original ideal experiment's common mass. -/
theorem game_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat) (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    TotalLaw attempts
      (1674813 + adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter)
      (operationalIdealGame adversary parameter scalar auxiliary)
      (game attempts adversary parameter scalar auxiliary) := by
  rw [← exactGame_eq]
  have law := (setup_law attempts).bind fun prepared =>
    continuation_law attempts adversary parameter scalar auxiliary prepared.1 prepared.2 (initial initialMetadata)
  have closed := law.weaken (second := 1674813 + adversary.preQueryBudget parameter +
    adversary.inputQueryBudget parameter + adversary.decisionQueryBudget parameter) (by omega)
  simpa only [exactGame, game, PMF.bind_map, Function.comp_def] using closed

/-- Arbitrary fallback decisions obey the same finite retry residual. -/
theorem game_error [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    advantage (operationalIdealGame adversary parameter scalar auxiliary)
      (game 256 adversary parameter scalar auxiliary) ≤
      cutoffResidual (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter) := by
  convert (game_law 256 adversary parameter scalar auxiliary).advantage using 1
  simp only [cutoffResidual, Nat.cast_add, inv_pow, div_eq_mul_inv]
  ring

/-- The total finite simulator preserves the concrete 100-bit privacy bound. -/
theorem privacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness) :
    WorkPerAdvantage 100
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter + 1)
      (advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (game 256 adversary parameter scalar auxiliary)) := by
  let queries := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
    adversary.decisionQueryBudget parameter
  by_cases small : queries < 2 ^ 100
  · have first := operational_small_error adversary parameter scalar auxiliary witness small
    have second := game_error adversary parameter scalar auxiliary
    have triangle := abs_sub_le
      ((ThreePhase.realGame adversary parameter scalar auxiliary witness) true).toReal
      ((operationalIdealGame adversary parameter scalar auxiliary) true).toReal
      ((game 256 adversary parameter scalar auxiliary) true).toReal
    have bound : advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
        (game 256 adversary parameter scalar auxiliary) ≤
        adaptiveErrorEnvelope queries + cutoffResidual queries :=
      triangle.trans (add_le_add first second)
    exact (mul_le_mul_of_nonneg_right bound (by positivity)).trans (cutoffEnvelope_has100Bits queries)
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

attribute [local irreducible] setup setupCode execute countedProgram
  SimulatorSamplingCost.onlineWithCost selected Cost.executeTotalCost

/-- This bound covers the actual setup, all three external phases, and the total encoder. -/
theorem resources [FieldCertificate] [GroupCertificate] {Aux Seed : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (random : (width : Nat) → Seed → Fin (2 ^ width) × Seed)
    (setupSeed onlineSeed : Seed) :
    let prepared := (setup 256).run random setupSeed
    let cache := prepared.1.1.1.1
    let table := prepared.1.1.1.2
    let n := adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
      836423 + adversary.decisionQueryBudget parameter
    let draws := 838390 + n
    let bits := draws * (257 * 256)
    ∀ before : (adversary.Before × SparseState) × Nat × Nat,
      before ∈ (ExternalBits.runTotalWithResources 256
        (adversary.prepare parameter auxiliary) (initial initialMetadata) 0).support →
    ∀ chosen : ((AffineInput × adversary.After) × SparseState) × Nat × Nat,
      chosen ∈ (ExternalBits.runTotalWithResources 256
        (adversary.chooseInput parameter table auxiliary before.1.1) before.1.2
        (adversary.preQueryBudget parameter)).support →
    let encoded := execute random 256 cache chosen.1.1.1
      ((Garbling.garbledCircuit construction).function scalar chosen.1.1.1) chosen.1.2 onlineSeed
      (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter)
    ∀ decided : (Bool × SparseState) × Nat × Nat,
      decided ∈ (ExternalBits.runTotalWithResources 256
        (adversary.decide parameter table encoded.1.1 auxiliary chosen.1.1.2) encoded.1.2.1
        (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter + 836423)).support →
      prepared.1.1.2 + before.2.1 + chosen.2.1 + encoded.2.2.1 + decided.2.1 ≤
        53788704 + n * (10 * n + 16) ∧
      prepared.2 + before.2.2 + chosen.2.2 + encoded.2.2.2 + decided.2.2 ≤ bits ∧
      prepared.1.1.2 + before.2.1 + chosen.2.1 + encoded.2.2.1 + decided.2.1 +
        4 * (prepared.2 + before.2.2 + chosen.2.2 + encoded.2.2.2 + decided.2.2) + draws ≤
          53788704 + n * (10 * n + 16) + 4 * bits + draws ∧
      Nonempty (Cost.StateBound decided.1.2 n) := by
  dsimp only
  intro before beforeReached chosen chosenReached
  let prepared := (setup 256).run random setupSeed
  let sample := (SimulatorSamplingCost.onlineWithCost.total 256).run random onlineSeed
  have phase := PhaseCost.total_all_phase_bound 256 random sample.1.2
    (adversary.prepare parameter auxiliary)
    (fun prior => adversary.chooseInput parameter prepared.1.1.1.2 auxiliary prior)
    (fun selectedInput => countedProgram prepared.1.1.1.1 selectedInput.1
      ((Garbling.garbledCircuit construction).function scalar selectedInput.1) sample.1.1.1)
    (fun selectedInput result => adversary.decide parameter prepared.1.1.1.2 result.1 auxiliary selectedInput.2)
    before beforeReached chosen chosenReached
  intro decided decidedReached
  simp only [execute] at decidedReached
  have closed := phase decided decidedReached
  have setupWork := setup_work random 256 setupSeed
  have onlineWork := execute_local random 256 prepared.1.1.1.1 chosen.1.1.1
    ((Garbling.garbledCircuit construction).function scalar chosen.1.1.1) chosen.1.2 onlineSeed
    (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter)
  have setupBits := setup_bits random 256 setupSeed
  have onlineBits := Code.total_bits random 256 SimulatorSamplingCost.onlineWithCost
    SimulatorSamplingCost.online_size onlineSeed
  have totalWork := Nat.add_le_add (Nat.add_le_add_right setupWork 51183699) closed.1
  have totalBits := Nat.add_le_add (Nat.add_le_add setupBits onlineBits) closed.2.1
  simp only [execute, prepared] at onlineWork ⊢
  dsimp only [sample, prepared] at closed totalWork totalBits
  simp only [Nat.add_mul] at totalBits
  refine ⟨?_, ?_, ?_, closed.2.2⟩ <;> omega

end
end SimulatorMachine.TotalImplementation
end Kriterion.ArgoMAC.Security
