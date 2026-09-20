import Proof.Privacy.Simulator.Arithmetic.SharedSourceProgram
import Proof.Privacy.Simulator.Arithmetic.ProgramCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine
noncomputable section

/-- The public program keeps every adaptive query and private sample. -/
def sharedExternalProgram {A : Type} : {budget : Nat} →
    OracleProgram SharedSimulatorMachine.sharedSpec A budget →
      OracleProgram SharedSimulatorMachine.combinedSpec A budget
  | _, .pure distribution => .pure distribution
  | _, .query request next => .query (.inr request) (fun value => sharedExternalProgram (next value))
  | _, .sample distribution next => .sample distribution (fun value => sharedExternalProgram (next value))

/-- The public program runs under the exact shared recording oracle. -/
theorem sharedExternalProgram_run {A : Type} {budget : Nat}
    (program : OracleProgram SharedSimulatorMachine.sharedSpec A budget) (state : SharedSimulatorMachine.SharedState) :
    (sharedExternalProgram program).run SharedSimulatorMachine.combinedEager state = program.run idealOracleHandler state := by
  induction program generalizing state with
  | pure distribution => simp only [sharedExternalProgram, OracleProgram.run_pure]
  | query request next ih => simp only [sharedExternalProgram, OracleProgram.run_query, SharedSimulatorMachine.combinedEager, ih]
  | sample distribution next ih => simp only [sharedExternalProgram, OracleProgram.run_sample, ih]

/-- The online source uses the complete shared valid or invalid schedule. -/
def sharedOnlineProgram [FieldCertificate] [GroupCertificate]
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Option Point) :
    OracleProgram SharedSimulatorMachine.combinedSpec Garbling.Labels 836423 :=
  match output with
  | none => (Program.weaken (sharedCombinedProgram (invalidProgram frame input)) (by decide : 3810 ≤ 836423)).toOracle
  | some point => .sample SimulatorSampling.online.law fun sample =>
      (sharedCombinedProgram (validProgram frame input point (Vector.ofFn sample.1) sample.2)).toOracle

/-- The online program changes only the oracle field of the private circuit frame. -/
theorem sharedOnlineProgram_run [FieldCertificate] [GroupCertificate]
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Option Point)
    (oracle : SharedSimulatorMachine.SharedState) :
    (sharedOnlineProgram frame input output).run SharedSimulatorMachine.combinedEager oracle =
      (Shared.Simulator.simulator.simulateEncode {frame with oracle} input output).map
        (fun result => (result.1, result.2.oracle)) := by
  cases output with
  | none =>
      have source := sharedCombined_invalid_run {frame with oracle} input
      simp only [sharedOnlineProgram, Program.toOracle_run, Program.run_weaken]
      rw [show invalidProgram frame input = invalidProgram {frame with oracle} input from rfl, source]
      simp only [Shared.Simulator.simulator, PMF.pure_map]
  | some point =>
      simp only [sharedOnlineProgram, OracleProgram.run_sample, Program.toOracle_run]
      have source (sample : ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase))) :=
        sharedCombined_valid_run {frame with oracle} input point (Vector.ofFn sample.1) sample.2
      have unchanged (sample : ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase))) :
          validProgram frame input point (Vector.ofFn sample.1) sample.2 =
            validProgram {frame with oracle} input point (Vector.ofFn sample.1) sample.2 := rfl
      simp only [unchanged, source, Shared.Simulator.simulator, PMF.map_comp]
      rw [show SimulatorSampling.online.law = PMF.uniformOfFintype _ from SimulatorSampling.online_uniform]
      rfl

/-- The complete source program keeps both adversary phases and the online command schedule. -/
def sharedAdaptiveProgram [FieldCertificate] [GroupCertificate]
    {First Result : Type} {firstBudget secondBudget : Nat}
    (frame : Shared.Simulator.State)
    (choose : OracleProgram SharedSimulatorMachine.sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram SharedSimulatorMachine.sharedSpec Result secondBudget) :
    OracleProgram SharedSimulatorMachine.combinedSpec Result (firstBudget + (836423 + secondBudget)) :=
  ThreePhase.append (fun selected =>
    ThreePhase.append (fun labels => sharedExternalProgram (decide selected labels))
      (sharedOnlineProgram frame (input selected) (output selected))) (sharedExternalProgram choose)

/-- The whole source program has the exact shared simulator law across both adaptive phases. -/
theorem sharedAdaptiveProgram_run [FieldCertificate] [GroupCertificate]
    {First Result : Type} {firstBudget secondBudget : Nat}
    (frame : Shared.Simulator.State)
    (choose : OracleProgram SharedSimulatorMachine.sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram SharedSimulatorMachine.sharedSpec Result secondBudget)
    (oracle : SharedSimulatorMachine.SharedState) :
    (sharedAdaptiveProgram frame choose input output decide).run SharedSimulatorMachine.combinedEager oracle =
      (choose.run idealOracleHandler oracle).bind fun selected =>
        (Shared.Simulator.simulator.simulateEncode {frame with oracle := selected.2}
          (input selected.1) (output selected.1)).bind fun encoded =>
            (decide selected.1 encoded.1).run idealOracleHandler encoded.2.oracle := by
  simp only [sharedAdaptiveProgram, ThreePhase.run_append, sharedExternalProgram_run,
    sharedOnlineProgram_run, PMF.bind_map, Function.comp_def]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
