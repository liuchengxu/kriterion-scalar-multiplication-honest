import Proof.Privacy.Simulator.Arithmetic.SharedTotalAdaptiveProgram
import Proof.Privacy.Simulator.Arithmetic.SharedCommandListProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

private theorem sharedProgram_map {A B : Type} {budget : Nat} (f : A → B)
    (program : Program SimulatorMachine.spec A budget) :
    sharedCombinedProgram (.map f program) = .map f (sharedCombinedProgram program) := rfl

private theorem sharedProgram_bind {A B : Type} {first second : Nat}
    (program : Program SimulatorMachine.spec A first) (next : A → Program SimulatorMachine.spec B second) :
    sharedCombinedProgram (.bind program next) = .bind (sharedCombinedProgram program)
      (fun value => sharedCombinedProgram (next value)) := rfl

private theorem sharedProgram_weaken {A : Type} {first second : Nat}
    (program : Program SimulatorMachine.spec A first) (bound : first ≤ second) :
    sharedCombinedProgram (.weaken program bound) = .weaken (sharedCombinedProgram program) bound := rfl

/-- The invalid source executes the exact curve command list before it returns labels. -/
theorem sharedInvalidProgram_cutoff [FieldCertificate] (frame : Shared.Simulator.State)
    (input : AffineInput) (attempts : Nat) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts)
      (sharedCombinedProgram (invalidProgram frame input)).toOracle state =
      (sharedCommandListCutoff attempts
        ((scheduleCommands ((frame.selectedCurve input).schedule input (frame.labels input).inputMac)).map sharedCommand)
        state).map (Option.map fun result => (frame.labels input, result.2)) := by
  simp only [invalidProgram, sharedProgram_map, sharedProgram_weaken, Program.cutoffLaw_toOracle,
    Program.cutoffLaw, sharedCombinedCommands_cutoff]

/-- The valid source links labels and then executes the exact complete command list. -/
theorem sharedValidProgram_cutoff [FieldCertificate] [GroupCertificate]
    (frame : Shared.Simulator.State) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase)
    (attempts : Nat) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts)
      (sharedCombinedProgram (validProgram frame input output free scales)).toOracle state =
      bindCutoff (runSampledCutoff (sharedSourceCutoff attempts)
        (sharedCombinedProgram (link (frame.selectedCurve input) input (frame.labels input).inputMac)).toOracle state)
        fun linked => (sharedCommandListCutoff attempts
          ((scheduleCommands (pipelineGateSchedule (frame.selectedCurve input)
            (frame.selectedPoints input output free scales) input (frame.labels input).inputMac linked.1)).map sharedCommand)
          linked.2).map (Option.map fun result => (frame.labels input, result.2)) := by
  simp only [validProgram, sharedProgram_bind, sharedProgram_map, sharedProgram_weaken,
    Program.cutoffLaw_toOracle, Program.cutoffLaw, sharedCombinedCommands_cutoff]

/-- The invalid online branch adds no private sampling or hidden link calls. -/
theorem sharedOnlineTotalProgram_none [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (frame : Shared.Simulator.State) (input : AffineInput) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) (sharedOnlineTotalProgram attempts frame input none) state =
      (sharedCommandListCutoff attempts
        ((scheduleCommands ((frame.selectedCurve input).schedule input (frame.labels input).inputMac)).map sharedCommand)
        state).map (Option.map fun result => (frame.labels input, result.2)) := by
  simpa only [sharedOnlineTotalProgram, Program.cutoffLaw_toOracle, Program.cutoffLaw] using
    sharedInvalidProgram_cutoff frame input attempts state

/-- The valid online branch samples its bounded private coin before the link and command list. -/
theorem sharedOnlineTotalProgram_some [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (frame : Shared.Simulator.State) (input : AffineInput) (output : Point) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) (sharedOnlineTotalProgram attempts frame input (some output)) state =
      (SimulatorSampling.online.total attempts).law.bind fun sample =>
        bindCutoff (runSampledCutoff (sharedSourceCutoff attempts)
          (sharedCombinedProgram (link (frame.selectedCurve input) input (frame.labels input).inputMac)).toOracle state)
          fun linked => (sharedCommandListCutoff attempts
            ((scheduleCommands (pipelineGateSchedule (frame.selectedCurve input)
              (frame.selectedPoints input output (Vector.ofFn sample.1) sample.2) input
              (frame.labels input).inputMac linked.1)).map sharedCommand) linked.2).map
                (Option.map fun result => (frame.labels input, result.2)) := by
  simp only [sharedOnlineTotalProgram, runSampledCutoff, sharedValidProgram_cutoff]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
