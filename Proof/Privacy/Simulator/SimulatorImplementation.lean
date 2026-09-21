import Proof.Privacy.Simulator.SimulatorRejectionCost
import Proof.Privacy.Simulator.SimulatorOfflineSetup
import Proof.Privacy.Simulator.SimulatorPublicCost
import Proof.Privacy.Simulator.SimulatorSamplingCost
import Proof.Privacy.Simulator.SimulatorPrivateCache
import Proof.Privacy.Simulator.SimulatorMachineLift
import Proof.Privacy.Simulator.SimulatorFinitePrivacy
import Proof.Privacy.Simulator.SimulatorScheduleCost
import Proof.Privacy.Simulator.SimulatorLinkCost
import Proof.Privacy.Simulator.SimulatorLabels
import Proof.Privacy.Simulator.SimulatorCommandCost
import Proof.Privacy.Simulator.SimulatorMachineCost

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling SimulatorScheduleCost SimulatorCommandCost
namespace SimulatorMachine
namespace Implementation

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000
attribute [local irreducible] SimulatorRejectionCost.PositiveWidths

/-- This expression reads the cached curve targets. -/
def hashWithCost (curve : PreparedCurve) (input : AffineInput) : BaseField × Nat :=
  (curveResultExpr curve.request input curve.tables.x3.targets curve.tables.x5.targets
    curve.tables.x7.targets curve.tables.y4.targets curve.tables.y6.targets).run

theorem hashWithCost_value (curve : PreparedCurve) (input : AffineInput) :
    (hashWithCost curve input).1 = curve.request.result input :=
  curveResultExpr_value _ _ _ _ _ _ _

theorem hashWithCost_bound (curve : PreparedCurve) (input : AffineInput) :
    (hashWithCost curve input).2 ≤ 6500 :=
  curveResultExpr_bound _ _ _ _ _ _ _

private theorem command_bound (prepared : Prepared) (input : AffineInput)
    (original linked : InputMac) :
    (scheduleCommandsWithCost (prepared.scheduleWithCost input original linked).1).1.length ≤ 835914 := by
  rw [scheduleCommandsWithCost_value]
  apply (scheduleCommands_length _).trans
  rw [Prepared.scheduleWithCost_value, pipelineGateSchedule_length_value]

private def checkedCommands (compiled : {value : List FixedCommand × Nat // value.1.length ≤ 835914}) :
    Program spec Unit 835914 := .weaken (commands compiled.1.1) compiled.2

private theorem checkedCommands_run
    (compiled : {value : List FixedCommand × Nat // value.1.length ≤ 835914}) (oracle : SimulatorState) :
    (checkedCommands compiled).run handler oracle = ((), executeFixedCommands oracle compiled.1.1) := by
  simp only [checkedCommands, Program.run_weaken, commands_run]

/-- This helper keeps the linked value abstract while it checks the command index. -/
private def validTail (input : AffineInput) (labels : Garbling.Labels × Nat) (prepared : Prepared × Nat)
    (hashCost : Nat) (linked : InputMac × Nat) : Program spec (Garbling.Labels × Nat) 835914 :=
  let schedule := prepared.1.scheduleWithCost input labels.1.inputMac linked.1
  let compiled : {value : List FixedCommand × Nat // value.1.length ≤ 835914} :=
    ⟨scheduleCommandsWithCost schedule.1, command_bound prepared.1 input labels.1.inputMac linked.1⟩
  .map (fun _ => (labels.1, labels.2 + prepared.2 + hashCost + linked.2 + schedule.2 + compiled.1.2))
    (checkedCommands compiled)

private theorem validTail_run (input : AffineInput) (labels : Garbling.Labels × Nat)
    (prepared : Prepared × Nat) (hashCost : Nat) (linked : InputMac × Nat) (oracle : SimulatorState) :
    ((validTail input labels prepared hashCost linked).run handler oracle).1.1 = labels.1 ∧
      ((validTail input labels prepared hashCost linked).run handler oracle).2 =
        programGateSchedule oracle (pipelineGateSchedule prepared.1.curve.request prepared.1.points input
          labels.1.inputMac linked.1) := by
  simp only [validTail, Program.run_map, checkedCommands_run, scheduleCommandsWithCost_value,
    scheduleCommands_correct, Prepared.scheduleWithCost_value]; exact ⟨trivial, trivial⟩

private def validCached (input : AffineInput) (labels : Garbling.Labels × Nat) (prepared : Prepared × Nat) :
    Program spec (Garbling.Labels × Nat) 836423 :=
  let hash := hashWithCost prepared.1.curve input
  .bind (LinkCost.linkWithCost hash.1 input labels.1.inputMac) (validTail input labels prepared hash.2)

private theorem bind_result {A B State : Type} {first second : Nat}
    (h : OracleHandler spec State) (source : Program spec A first)
    (next : A → Program spec B second) (state target : State) (answer : A)
    (sourceLaw : source.run h state = (answer, target)) :
    (Program.bind source next).run h state = (next answer).run h target :=
  (Program.run_bind h source next state).trans
    (congrArg (fun result : A × State => (next result.1).run h result.2) sourceLaw)

private theorem validCached_run (input : AffineInput) (labels : Garbling.Labels × Nat)
    (prepared : Prepared × Nat) (oracle : SimulatorState) :
    ((validCached input labels prepared).run handler oracle).1.1 = labels.1 ∧
      ((validCached input labels prepared).run handler oracle).2 =
        programGateSchedule oracle (pipelineGateSchedule prepared.1.curve.request prepared.1.points input
          labels.1.inputMac (linkedPointInputMac oracle prepared.1.curve.request input labels.1.inputMac)) := by
  have linkLaw := LinkCost.linkWithCost_run prepared.1.curve.request input labels.1.inputMac
    (hashWithCost prepared.1.curve input).1 (hashWithCost_value _ _) oracle
  have runLaw := bind_result handler _ (validTail input labels prepared (hashWithCost prepared.1.curve input).2)
    oracle oracle (linkedPointInputMac oracle prepared.1.curve.request input labels.1.inputMac, 6110) linkLaw
  have tailLaw := validTail_run input labels prepared (hashWithCost prepared.1.curve input).2
    (linkedPointInputMac oracle prepared.1.curve.request input labels.1.inputMac, 6110) oracle
  exact ⟨(congrArg (fun result => result.1.1) runLaw).trans tailLaw.1,
    (congrArg Prod.snd runLaw).trans tailLaw.2⟩

/-- The cached encoder constructs its labels and selected schedules once. -/
def valid [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) : Program spec (Garbling.Labels × Nat) 836423 :=
  validCached input (labelsWithCost coin.2.1 input) (prepareWithCost (privateView coin) tables input point free scales)

/-- The cached encoder has exactly the original eager label and oracle result. -/
theorem valid_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) (oracle : SimulatorState) :
    ((valid coin tables input point free scales).run handler oracle).1.1 =
        (privateView coin).labels input ∧
      ((valid coin tables input point free scales).run handler oracle).2 =
        ((privateState coin oracle).programForOutput input point free scales.get).oracle := by
  have law := validCached_run input (labelsWithCost coin.2.1 input)
    (prepareWithCost (privateView coin) tables input point free scales) oracle
  have curve : (privateState coin oracle).selectedCurve input = (privateView coin).selectedCurve input := rfl
  have points : (privateState coin oracle).selectedPoints input point free scales.get =
      (privateView coin).selectedPoints input point free scales.get := rfl
  have labels : (privateState coin oracle).labels input = (privateView coin).labels input := rfl
  have state : (privateState coin oracle).oracle = oracle := rfl
  simpa only [valid, prepareWithCost_curve, prepareWithCost_points, (labelsWithCost_spec coin input).1,
    CircuitSimulatorState.programForOutput, CircuitSimulatorState.selectedSchedule,
    linkedPipelineGateSchedule, curve, points, labels, state] using law

/-- The cached arithmetic cost is independent of the oracle answers. -/
theorem valid_local_bound [FieldCertificate] [GroupCertificate] {State : Type}
    (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (point : Point) (free : Vector Point 90)
    (scales : Vector NonZeroBase FieldMacToECMac.outputMacCount) (state : State) :
    ((valid coin tables input point free scales).run oracleHandler state).1.2 ≤ 50000000 := by
  have prepared := prepareWithCost_bound (privateView coin) tables input point free scales
  have hashed := hashWithCost_bound (prepareWithCost (privateView coin) tables input point free scales).1.curve input
  have compiled (linked : InputMac) := scheduleCommandsWithCost_bound
    ((prepareWithCost (privateView coin) tables input point free scales).1.scheduleWithCost
      input (labelsWithCost coin.2.1 input).1.inputMac linked).1
  simp only [Prepared.scheduleWithCost_value, pipelineGateSchedule_length_value] at compiled
  simp only [valid, validCached, validTail, Program.run_bind, Program.run_map]
  rw [LinkCost.linkWithCost_cost, Prepared.scheduleWithCost_count, (labelsWithCost_spec coin input).2]
  have current := compiled ((LinkCost.linkWithCost
    (hashWithCost (prepareWithCost (privateView coin) tables input point free scales).1.curve input).1
    input (labelsWithCost coin.2.1 input).1.inputMac).run oracleHandler state).1.1
  simp only [Prepared.scheduleWithCost_value]
  omega


private theorem curve_command_bound (curve : PreparedCurve) (input : AffineInput) (mac : InputMac) :
    (scheduleCommandsWithCost (curveScheduleWithCost curve.request input mac curve.tables).1).1.length ≤ 3810 := by
  rw [scheduleCommandsWithCost_value]
  apply (scheduleCommands_length _).trans
  rw [curveScheduleWithCost_value, CurveGateRequest.schedule_length]
  decide

/-- The invalid encoder caches only the curve path. -/
def invalid (coin : OfflineCoin) (tables : SimulatorTables (privateView coin)) (input : AffineInput) :
    Program spec (Garbling.Labels × Nat) 3810 :=
  let labels := labelsWithCost coin.2.1 input
  let curve := prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve
  let schedule := curveScheduleWithCost curve.1.request input labels.1.inputMac curve.1.tables
  let compiled := scheduleCommandsWithCost schedule.1
  .map (fun _ => (labels.1, labels.2 + curve.2 + schedule.2 + compiled.2))
    (.weaken (commands compiled.1) (curve_command_bound curve.1 input labels.1.inputMac))

/-- The cached invalid encoder has exactly the original eager result. -/
theorem invalid_run (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (oracle : SimulatorState) :
    ((invalid coin tables input).run handler oracle).1.1 = (privateView coin).labels input ∧
      ((invalid coin tables input).run handler oracle).2 =
        ((invalidProgram (privateView coin) input).run handler oracle).2 := by
  simp only [invalid, invalidProgram, Program.run_map, Program.run_weaken]
  simp only [commands_run,
    scheduleCommandsWithCost_value, scheduleCommands_correct, curveScheduleWithCost_value,
    prepareCurveWithCost_value, (labelsWithCost_spec coin input).1,
    CircuitSimulatorState.selectedCurve]
  exact ⟨trivial, trivial⟩

/-- The invalid encoder has the same fixed local bound under every handler. -/
theorem invalid_local_bound {State : Type} (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (state : State) :
    ((invalid coin tables input).run oracleHandler state).1.2 ≤ 50000000 := by
  have curve := prepareCurveWithCost_bound (privateView coin).curve input (privateView coin).bridgeKey tables.curve
  have compiled := scheduleCommandsWithCost_bound
    (curveScheduleWithCost
      (prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve).1.request
      input (labelsWithCost coin.2.1 input).1.inputMac
      (prepareCurveWithCost (privateView coin).curve input (privateView coin).bridgeKey tables.curve).1.tables).1
  simp only [curveScheduleWithCost_value, CurveGateRequest.schedule_length, coordinateBitCount] at compiled
  simp only [invalid, Program.run_map, curveScheduleWithCost_count, (labelsWithCost_spec coin input).2,
    curveScheduleWithCost_value]
  omega

/-- The selected encoder keeps its actual deterministic operation counter. -/
def selected [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) :
    Program spec (Garbling.Labels × Nat) (onlineBudget output) :=
  match output with
  | none => invalid coin tables input
  | some point => .map (fun answer => (answer.1, answer.2 + 362))
      (valid coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2))

/-- The selected encoder has a fixed local bound under every handler. -/
theorem selected_local_bound [FieldCertificate] [GroupCertificate] {State : Type}
    (oracleHandler : OracleHandler spec State)
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) (state : State) :
    ((selected coin tables input output sample).run oracleHandler state).1.2 ≤ 51000000 := by
  cases output with
  | none => exact (invalid_local_bound oracleHandler coin tables input state).trans (by decide)
  | some point =>
      have bound := valid_local_bound oracleHandler coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2) state
      simp only [selected, Program.run_map]
      omega


/-- This projection keeps the cached encoder's exact semantic result. -/
theorem selected_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point)
    (sample : (Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase))
    (oracle : SimulatorState) :
    ((selected coin tables input output sample).map Prod.fst).run handler oracle =
      match output with
      | none => (invalidProgram (privateView coin) input).run handler oracle
      | some point => (validProgram (privateView coin) input point (Vector.ofFn sample.1) sample.2).run handler oracle := by
  cases output with
  | none =>
      have result := invalid_run coin tables input oracle
      apply Prod.ext
      · exact result.1
      · exact result.2
  | some point =>
      have result := valid_run coin tables input point (Vector.ofFn sample.1) (Vector.ofFn sample.2) oracle
      have same : (Vector.ofFn sample.2).get = sample.2 := funext (Vector.get_ofFn sample.2)
      simp only [selected, Program.run_map]
      conv_rhs => rw [← same]
      rw [validProgram_private_run]
      generalize (valid coin tables input point (Vector.ofFn sample.1)
        (Vector.ofFn sample.2)).run handler oracle = answer at result ⊢
      generalize ((privateState coin oracle).programForOutput input point (Vector.ofFn sample.1)
        (Vector.ofFn sample.2).get).oracle = nextState at result ⊢
      generalize (privateView coin).labels input = labels at result ⊢
      exact @Prod.ext Garbling.Labels SimulatorState _ _ result.1 result.2

/-- The cached encoder samples its online coin before it executes the selected path. -/
noncomputable def encoding [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) :
    OracleProgram spec Garbling.Labels (onlineBudget output) :=
  .sample online.law (fun sample => ((selected coin tables input output sample).map Prod.fst).toOracle)

/-- The cached online encoder has the exact original eager distribution. -/
theorem encoding_run [FieldCertificate] [GroupCertificate]
    (coin : OfflineCoin) (tables : SimulatorTables (privateView coin))
    (input : AffineInput) (output : Option Point) (oracle : SimulatorState) :
    (encoding coin tables input output).run handler oracle =
      (encodeProgram coin input output).run handler oracle := by
  cases output with
  | none =>
      simp only [encoding, OracleProgram.run_sample, Program.toOracle_run, selected_run, encodeProgram]
      simp
  | some point =>
      simp only [encoding, OracleProgram.run_sample, Program.toOracle_run, selected_run,
        encodeProgram, ThreePhase.run_append, OracleProgram.run_pure, PMF.bind_map, Function.comp_def]

noncomputable section

/-- This exact game executes the cached encoder between the three adversary phases. -/
def continuation [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (cache : PrivateCache) (table : Pipeline.Table) (state : SparseState) : PMF Bool :=
  (runSampled externalHandler (adversary.prepare parameter auxiliary) state).bind (fun prepared =>
    (runSampled externalHandler
      (adversary.chooseInput parameter table auxiliary prepared.1) prepared.2).bind (fun selected =>
      (runSampled sparseHandler (encoding cache.coin cache.tables selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)) selected.2).bind
        (fun encoded => (runSampled externalHandler
          (adversary.decide parameter table encoded.1 auxiliary selected.1.2) encoded.2).map Prod.fst)))

/-- The cached program has its own full sparse completion law. -/
theorem continuation_exact [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (cache : PrivateCache) (state : SparseState) :
    (completion state).bind (eagerContinuation adversary parameter scalar auxiliary cache.coin) =
      continuation adversary parameter scalar auxiliary cache (privateView cache.coin).table state := by
  unfold eagerContinuation continuation
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled externalHandler (adversary.prepare parameter auxiliary) state))
  funext prepared
  simp only
  rw [joint_bind idealOracleHandler externalHandler completion _ _ (external_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled externalHandler
    (adversary.chooseInput parameter (privateView cache.coin).table auxiliary prepared.1) prepared.2))
  funext selected
  simp only
  have same : (encodeProgram cache.coin selected.1.1
      ((Garbling.garbledCircuit construction).function scalar selected.1.1)).run handler =
      (encoding cache.coin cache.tables selected.1.1
        ((Garbling.garbledCircuit construction).function scalar selected.1.1)).run handler := by
    funext oracle
    exact (encoding_run cache.coin cache.tables _ _ oracle).symm
  rw [same]
  rw [joint_bind handler sparseHandler completion _ _ (sparse_adaptive_joint _ _)]
  apply congrArg (PMF.bind (runSampled sparseHandler
    (encoding cache.coin cache.tables selected.1.1
      ((Garbling.garbledCircuit construction).function scalar selected.1.1)) selected.2))
  funext encoded
  simp only
  have last := congrArg (fun distribution : PMF (Bool × SimulatorState) => distribution.map Prod.fst)
    (external_adaptive_joint
      (adversary.decide parameter (privateView cache.coin).table encoded.1 auxiliary selected.1.2) encoded.2)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at last
  have finish (output : Bool × SparseState) :
      (completion output.2).map (fun _ => output.1) = PMF.pure output.1 := PMF.map_const _ _
  simp_rw [finish] at last
  simpa only [PMF.map, Function.comp_def] using last

/-- The array sampler supplies the actual cached simulator state. -/
def exactGame [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  offlineReady.law.bind (fun prepared =>
    continuation adversary parameter scalar auxiliary prepared.1 prepared.2 (initial initialMetadata))

/-- The actual cached implementation has exactly the original ideal decision distribution. -/
theorem exactGame_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : ThreePhase.Adversary Aux) (parameter : Nat)
    (scalar : NonZeroScalar) (auxiliary : Aux) :
    exactGame adversary parameter scalar auxiliary = operationalIdealGame adversary parameter scalar auxiliary := by
  unfold exactGame operationalIdealGame
  rw [offlineReady, Code.map_law, ← offlineArrays_law, PMF.bind_map, PMF.bind_map]
  apply congrArg (PMF.bind offlineArrays.law)
  funext arrays
  dsimp only [Function.comp_def, ready]
  rw [tableWithCost_value]
  have exact := continuation_exact adversary parameter scalar auxiliary (cacheWithCost arrays).1 (initial initialMetadata)
  rw [cacheWithCost_coin] at exact
  rw [← exact, ← continuation_law]

end
end Implementation
end SimulatorMachine
end Kriterion.ArgoMAC.Security
