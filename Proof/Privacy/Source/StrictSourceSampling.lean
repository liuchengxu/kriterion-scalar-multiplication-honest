import Proof.Privacy.Source.StrictGateSource
import Proof.Privacy.Bounds.SharedMachineArithmetic
import Proof.Privacy.Simulator.SimulatorTotalSampling
import Proof.Privacy.Simulator.Arithmetic.SharedExactSourceGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions SimulatorMachine
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The strict frame executes both adaptive phases with checked programming. -/
def sharedStrictFrameDecision [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : PMF ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)))
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) (frame : Shared.Simulator.State) : PMF Bool :=
  ((adversary.chooseInput parameter frame.table auxiliary).run idealOracleHandler frame.oracle).bind fun selected =>
    online.bind fun random =>
      let labels := frame.labels selected.1.1
      let final := sharedProgramSelectedGateView selected.2 selected.1.1 labels.inputMac
        (frame.selectedCurve selected.1.1,
          (checkedScalarMultiplication scalar.value selected.1.1).map fun point =>
            frame.selectedPoints selected.1.1 point (Vector.ofFn random.1) random.2)
      if final.bad then PMF.pure false
      else ((adversary.decide parameter frame.table labels auxiliary selected.1.2).run idealOracleHandler final).map Prod.fst

/-- The strict source samples only private coins and uses the common public oracle. -/
def sharedStrictSourceDecision [FieldCertificate] [GroupCertificate] {Aux : Type}
    (offline : PMF SimulatorSampling.OfflineCoin)
    (online : PMF ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)))
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  offline.bind fun coin =>
    (OperationalOracle.publicCompletion (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
      sharedStrictFrameDecision online adversary parameter scalar auxiliary (Shared.Simulator.initialState coin oracle)

/-- The two private samplers consume 917653 finite draw allowances. -/
theorem sharedStrictSourceDecision_law [FieldCertificate] [GroupCertificate] {Aux : Type}
    (attempts : Nat)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    TotalLaw attempts 838389
      (sharedStrictSourceDecision SimulatorSampling.offline.law SimulatorSampling.online.law
        adversary parameter scalar auxiliary)
      (sharedStrictSourceDecision (SimulatorSampling.offline.total attempts).law (SimulatorSampling.online.total attempts).law
        adversary parameter scalar auxiliary) := by
  unfold sharedStrictSourceDecision sharedStrictFrameDecision
  change TotalLaw attempts (838208 + (181 + 0)) _ _
  apply (SimulatorSampling.Code.total_law attempts SimulatorSampling.offline).bind
  intro coin
  apply TotalLaw.sample
  intro oracle
  apply TotalLaw.sample
  intro selected
  exact (SimulatorSampling.Code.total_law attempts SimulatorSampling.online).bind
    (fun random => TotalLaw.exact attempts _)

/-- The private sampler error fits the existing machine allowance. -/
theorem sharedStrictSourceDecision_allowance [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    advantage
      (sharedStrictSourceDecision SimulatorSampling.offline.law SimulatorSampling.online.law
        adversary parameter scalar auxiliary)
      (sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law (SimulatorSampling.online.total 256).law
        adversary parameter scalar auxiliary) ≤
      sharedMachineCutoffAllowance (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  have bound := (sharedStrictSourceDecision_law 256 adversary parameter scalar auxiliary).advantage
  apply bound.trans
  simp only [sharedMachineCutoffAllowance, inv_pow, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) (adversary.firstQueryBudget parameter),
    Nat.cast_nonneg (α := ℝ) (adversary.secondQueryBudget parameter)]

private theorem sharedChoose_erase {Aux Result : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table) (data : GarblingOracleData)
    (follow : (AffineInput × adversary.State) × Shared.Simulator.OracleState → PMF Result) :
    (sharedGateSourceChoose adversary parameter auxiliary table data).bind
      (fun selected => follow ((selected.1, selected.2.1), selected.2.2.1)) =
      ((adversary.chooseInput parameter table auxiliary).run idealOracleHandler (sharedInitialSourceOracle data)).bind follow := by
  have law := congrArg (fun distribution => distribution.bind follow)
    (runOracleProgramWithTranscript_erase idealOracleHandler (adversary.chooseInput parameter table auxiliary)
      (sharedInitialSourceOracle data))
  simpa only [sharedGateSourceChoose, PMF.bind_map, Function.comp_def] using law

set_option backward.isDefEq.respectTransparency false in
/-- The exact private source has the strict ideal source's complete decision law. -/
theorem sharedStrictSourceDecision_exact [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    sharedStrictSourceDecision SimulatorSampling.offline.law SimulatorSampling.online.law
      adversary parameter scalar auxiliary =
    actualSharedIdealGateSourceRun scalar.value
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedStrictGateSourceObserve adversary parameter auxiliary table selected view rest.2) := by
  classical
  letI : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
  letI : Fintype SharedMaskRetainedTape := Fintype.ofFinite _
  letI : Nonempty SharedMaskRetainedTape := ⟨Classical.ofNonempty⟩
  letI : Fintype RetainedRowCoin := Fintype.ofFinite _
  letI : Nonempty RetainedRowCoin := ⟨Classical.ofNonempty⟩
  have stateLaw := congrArg (fun distribution : PMF Shared.Simulator.State =>
    distribution.bind (sharedStrictFrameDecision SimulatorSampling.online.law adversary parameter scalar auxiliary))
    (sharedRetainedSource_initialState_law parameter (Garbling.topology scalar))
  rw [ArithmeticSimulator.sharedTape_coinFirst] at stateLaw
  simp only [PMF.bind_map, Function.comp_def] at stateLaw
  unfold sharedStrictSourceDecision
  rw [OperationalOracle.public_initial, ← stateLaw, actualSharedIdealGateSource_eq_target]
  unfold sharedTargetGateSourceRun
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample) finite inferInstance)
    exact Subsingleton.elim _ _
  funext source
  have onlineUniform : SimulatorSampling.online.law = PMF.uniformOfFintype
      ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) := SimulatorSampling.online_uniform
  rw [onlineUniform]
  simp only [sharedStrictFrameDecision, sharedSourceInitialState,
    Shared.Simulator.initialState, CircuitSimulatorState.table, CircuitSimulatorState.labels,
    CircuitSimulatorState.selectedCurve, CircuitSimulatorState.selectedPoints,
    publicMaskTable, sharedInitialSourceOracle, sourceInputLabels,
    sharedStrictGateSourceObserve, checkedScalarMultiplication, Option.map_map]
  exact (sharedChoose_erase adversary parameter auxiliary (publicMaskTable source.2)
    source.1.val.2.2.2 _).symm

/-- Checked programming depends only on its oracles, fixed history, and failure flag. -/
theorem sharedCommands_fields (first second : Shared.Simulator.OracleState) (commands : List FixedCommand)
    (fixed : first.fixedOracle = second.fixedOracle) (enc : first.encOracle = second.encOracle)
    (hash : first.hashOracle = second.hashOracle) (history : first.fixedTranscript = second.fixedTranscript)
    (bad : first.bad = second.bad) :
    let a := Shared.Simulator.commands first commands
    let b := Shared.Simulator.commands second commands
    a.fixedOracle = b.fixedOracle ∧ a.encOracle = b.encOracle ∧ a.hashOracle = b.hashOracle ∧
      a.fixedTranscript = b.fixedTranscript ∧ a.bad = b.bad := by
  induction commands generalizing first second with
  | nil => exact ⟨fixed, enc, hash, history, bad⟩
  | cons command rest ih =>
    apply ih
    all_goals
      simp only [Shared.Simulator.execute, tryProgramFixed, history]
      split <;> simp only [programFixed, markBad, fixed, enc, hash, history, bad]

attribute [local irreducible] Shared.Simulator.commands

set_option backward.isDefEq.respectTransparency false in
/-- The strict selected-view decision ignores other query metadata. -/
theorem sharedStrictViewDecision_congr {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Bool budget)
    (first second : Shared.Simulator.OracleState) (input : AffineInput) (mac : InputMac) (view : SelectedGateView)
    (fixed : first.fixedOracle = second.fixedOracle) (enc : first.encOracle = second.encOracle)
    (hash : first.hashOracle = second.hashOracle) (history : first.fixedTranscript = second.fixedTranscript)
    (bad : first.bad = second.bad) :
    (let next := sharedProgramSelectedGateView first input mac view
      if next.bad then PMF.pure false else (program.run idealOracleHandler next).map Prod.fst) =
    (let next := sharedProgramSelectedGateView second input mac view
      if next.bad then PMF.pure false else (program.run idealOracleHandler next).map Prod.fst) := by
  have schedule : (match view.2 with
      | none => view.1.schedule input mac
      | some points => linkedPipelineGateSchedule first view.1 points input mac) =
      (match view.2 with
      | none => view.1.schedule input mac
      | some points => linkedPipelineGateSchedule second view.1 points input mac) := by
    cases view.2 <;> simp only [linkedPipelineGateSchedule, linkedPointInputMac, enc, hash]
  have fields := sharedCommands_fields first second
    (scheduleCommands (match view.2 with
      | none => view.1.schedule input mac
      | some points => linkedPipelineGateSchedule second view.1 points input mac)) fixed enc hash history bad
  have installed : sharedProgramSelectedGateView first input mac view =
      Shared.Simulator.commands first (scheduleCommands (match view.2 with
        | none => view.1.schedule input mac
        | some points => linkedPipelineGateSchedule second view.1 points input mac)) :=
    congrArg (fun values => Shared.Simulator.commands first (scheduleCommands values)) schedule
  rw [installed]
  simp only [sharedProgramSelectedGateView, Shared.Simulator.program]
  rw [fields.2.2.2.2]
  simp only [OperationalOracle.shared_public_result, fields.1, fields.2.1, fields.2.2.1]
  rfl


end
end Kriterion.ArgoMAC.Security
