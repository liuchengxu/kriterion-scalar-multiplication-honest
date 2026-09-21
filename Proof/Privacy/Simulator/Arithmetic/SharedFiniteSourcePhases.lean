import Proof.Privacy.Simulator.Arithmetic.SharedWireFiniteDecision

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

/-- The lifted public program has the exact external shared cutoff handler. -/
theorem sharedExternalProgram_cutoff (attempts : Nat) {Result : Type} {budget : Nat}
    (program : OracleProgram sharedSpec Result budget) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) (sharedExternalProgram program) state =
      runSampledCutoff (fun request => sharedSourceCutoff attempts (.inr request)) program state := by
  induction program generalizing state with
  | pure distribution => rfl
  | query request next ih => simp only [sharedExternalProgram, runSampledCutoff, ih]
  | sample distribution next ih => simp only [sharedExternalProgram, runSampledCutoff, ih]

/-- The finite adaptive program has the exact public-online-public cutoff composition. -/
theorem sharedAdaptiveTotalProgram_cutoff [FieldCertificate] [GroupCertificate]
    {First Result : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : Shared.Simulator.State) (choose : OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : First → Garbling.Labels → OracleProgram sharedSpec Result secondBudget) (state : SharedOracleSource) :
    runSampledCutoff (sharedSourceCutoff attempts) (sharedAdaptiveTotalProgram attempts frame choose input output decide) state =
      bindCutoff (runSampledCutoff (fun request => sharedSourceCutoff attempts (.inr request)) choose state) fun selected =>
        bindCutoff (runSampledCutoff (sharedSourceCutoff attempts)
          (sharedOnlineTotalProgram attempts frame (input selected.1) (output selected.1)) selected.2) fun encoded =>
            runSampledCutoff (fun request => sharedSourceCutoff attempts (.inr request)) (decide selected.1 encoded.1) encoded.2 := by
  simp only [sharedAdaptiveTotalProgram, sampledCutoff_append, sharedExternalProgram_cutoff]

/-- The finite reference has the same four phase boundaries as the actual machine protocol. -/
theorem sharedWireFiniteDecision_phases [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    sharedWireFiniteDecision adversary parameter scalar auxiliary =
      (SimulatorSampling.offline.total 256).law.bind fun coin =>
        (bindCutoff
          (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
            (sharedWireSourceChoose adversary parameter auxiliary coin) (initialSharedOracleSource emptySharedMetadata)) fun selected =>
          bindCutoff (runSampledCutoff (sharedSourceCutoff 256)
            (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) selected.1.1 (Shared.wireCircuit.function scalar selected.1.1)) selected.2) fun encoded =>
              runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
                (sharedWireSourceDecide adversary parameter auxiliary coin selected.1 encoded.1) encoded.2).map
                  (fun result => (result.map Prod.fst).getD false) := by
  simp only [sharedWireFiniteDecision, sharedFiniteSourceDecision, sharedAdaptiveTotalProgram_cutoff]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
