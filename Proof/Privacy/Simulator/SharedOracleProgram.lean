import Proof.Privacy.Simulator.SharedSimulator
import Proof.Privacy.Simulator.SimulatorOracleProgram
import Proof.Privacy.Simulator.OperationalSimulator

namespace Kriterion.ArgoMAC.Shared.Simulator.Source
open BN254 Cryptography Security
open Security.SimulatorMachine

/-- The source program reads and programs the three-slot oracle state. -/
def handler : OracleHandler spec OracleState
  | .read (.fixedForward index input), state => (state.fixedOracle.permutation (fixedIndex index) input, state)
  | .read (.fixedInverse index output), state => ((state.fixedOracle.permutation (fixedIndex index)).symm output, state)
  | .read (.encForward index input), state => (state.encOracle.permutation index input, state)
  | .read (.encInverse index output), state => ((state.encOracle.permutation index).symm output, state)
  | .read (.hash input), state => (state.hashOracle input, state)
  | .program command, state => ((), execute state command)

/-- The source interpreter keeps the shared command order. -/
theorem commands_run (values : List FixedCommand) (state : OracleState) :
    (SimulatorMachine.commands values).run handler state = ((), Simulator.commands state values) := by
  induction values generalizing state with
  | nil => rfl
  | cons command rest ih => exact ih (execute state command)

/-- The EncPRF vector reads the same encryption oracle in the shared state. -/
theorem encVector_run (count : Nat)
    (indices : Fin count → EncPRF.PermutationIndex) (inputs : Fin count → Block)
    (state : OracleState) :
    (encVector count indices inputs).run handler state =
      ((fun index => state.encOracle.permutation (indices index) (inputs index)), state) := by
  induction count with
  | zero =>
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
  | succ count ih =>
      simp only [encVector, Program.run, handler, ih]
      apply Prod.ext
      · funext index
        exact Fin.cases rfl (fun _ => rfl) index
      · rfl

theorem coordinate_run (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) (state : OracleState) :
    (coordinate keys axis bits mac).run handler state =
      (EncPRF.transformCoordinateMac state.encOracle keys axis bits mac, state) := by
  simp only [coordinate, Program.run, encVector_run]
  rfl

/-- The linking program uses the shared state's hash and encryption oracles. -/
theorem link_run (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (state : OracleState) :
    (link curve input mac).run handler state = (linkedPointInputMac state curve input mac, state) := by
  simp only [link, Program.run, handler, coordinate_run]
  rfl

/-- The valid source program executes the complete shared gate schedule. -/
theorem valid_run [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    (validProgram state input output free scales).run handler state.oracle =
      (state.labels input, program state.oracle (state.selectedSchedule input output free scales)) := by
  simp only [validProgram, Program.run_bind, link_run, Program.run_map,
    Program.run_weaken, commands_run, program, CircuitSimulatorState.selectedSchedule,
    linkedPipelineGateSchedule]

/-- The invalid source program executes only the shared curve schedule. -/
theorem invalid_run (state : State) (input : AffineInput) :
    (invalidProgram state input).run handler state.oracle =
      (state.labels input, program state.oracle
        ((state.selectedCurve input).schedule input (state.labels input).inputMac)) := by
  simp only [invalidProgram, Program.run, commands_run, program]

/-- These counts bound oracle operations. They do not count arithmetic instructions. -/
theorem valid_query_count [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Point) (free : Vector Point 90)
    (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    ((validProgram state input output free scales).runCount handler state.oracle).2 ≤ 836423 :=
  (Program.runCount_correct handler _ state.oracle).2

/-- The source program samples online coins before it programs the selected path. -/
noncomputable def encode [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) :
    OracleProgram spec Garbling.Labels (if output.isSome then 836423 else 3810) :=
  match output with
  | none => (invalidProgram state input).toOracle
  | some point => ThreePhase.append
      (fun sample => (validProgram state input point (Vector.ofFn sample.1) sample.2).toOracle)
      (.pure SimulatorSampling.online.law)

/-- The source interpreter gives the complete abstract shared simulator's online law. -/
theorem encode_run [FieldCertificate] [GroupCertificate] (state : State)
    (input : AffineInput) (output : Option Point) :
    ((encode state input output).run handler state.oracle).map
      (fun result => (result.1, {state with oracle := result.2})) =
      simulator.simulateEncode state input output := by
  cases output with
  | none =>
      simp only [encode, Program.toOracle_run, invalid_run, PMF.pure_map, simulator]
  | some point =>
      simp only [encode, ThreePhase.run_append, OracleProgram.run_pure,
        PMF.bind_map, Function.comp_def, Program.toOracle_run, valid_run,
        simulator]
      rw [show SimulatorSampling.online.law = PMF.uniformOfFintype _ from
        SimulatorSampling.online_uniform]
      simp only [PMF.map_bind, PMF.pure_map]
      rfl

end Kriterion.ArgoMAC.Shared.Simulator.Source
