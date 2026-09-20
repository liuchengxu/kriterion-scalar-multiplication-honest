import Proof.Privacy.Simulator.Arithmetic.CompiledChosenDecision

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
open GarbledCircuit.SimulatorProtocol
noncomputable section
attribute [local irreducible] compiledQueryCoupledSamples runProgram offlineSchedule compiledSetupJoint

private theorem cutoff_map_next {A B C : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (observe : B → C) :
    (bindCutoff source next).map (Option.map observe) =
      bindCutoff source (fun value => (next value).map (Option.map observe)) := by
  simp only [bindCutoff, PMF.map_bind]
  congr 1
  funext result
  cases result <;> simp only [PMF.pure_map, Option.map_none]

/-- The full joint experiment starts with the actual setup sampler and preserves every failure. -/
def compiledAdaptiveDecision [FieldCertificate] [GroupCertificate] {Aux : Type} (online : SharedOnlineJoint)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  (compiledSetupJoint 256 parameter).bind fun setup =>
    (compiledChosenDecision online adversary parameter scalar auxiliary setup.1 setup.2).map (fun result => result.getD false)

/-- The joint experiment has the exact complete bounded-machine game as its first marginal. -/
theorem compiledAdaptiveDecision_machine [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : SharedOnlineJoint) (implemented : CompiledOnlineCouplingLaw online)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 101) :
    compiledAdaptiveDecision online adversary parameter scalar auxiliary =
      GarbledCircuit.SimulatorProtocol.idealGame Shared.packedCircuit Wire.encoding 8887896
        (compiledMachine 256) adversary parameter scalar auxiliary := by
  rw [sharedParsedGame_phases]
  have setupLaw := compiledSetupJoint_parsed 256 parameter (by decide) compiledMachine_setupBudget
  change (compiledSetupJoint 256 parameter).map _ = sharedParsedSetup (compiledMachine 256) parameter at setupLaw
  rw [← setupLaw]
  simp only [compiledAdaptiveDecision, bindCutoff, PMF.bind_map, Option.map_some, PMF.map_bind]
  apply ThreePhase.bind_eq_on_support
  intro setup member
  exact congrArg (PMF.map (fun result : Option Bool => result.getD false))
    (compiledChosenDecision_law online implemented adversary parameter scalar auxiliary setup.1 setup.2 member small).1

/-- The joint experiment has the exact full finite-source game as its second marginal. -/
theorem compiledAdaptiveDecision_source [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : SharedOnlineJoint) (implemented : CompiledOnlineCouplingLaw online)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 101) :
    compiledAdaptiveDecision online adversary parameter scalar auxiliary =
      sharedWireFiniteDecision adversary parameter scalar auxiliary := by
  rw [sharedWireFiniteDecision_phases, ← compiledSetupJoint_source 256 parameter]
  simp only [compiledAdaptiveDecision, PMF.bind_map]
  apply ThreePhase.bind_eq_on_support
  intro setup member
  rw [(compiledChosenDecision_law online implemented adversary parameter scalar auxiliary setup.1 setup.2 member small).2]
  have moved := congrArg (PMF.map (fun result : Option Bool => result.getD false))
    (cutoff_map_next
      (runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
        (sharedWireSourceChoose adversary parameter auxiliary setup.2) (initialSharedOracleSource emptySharedMetadata))
      (fun selected => bindCutoff (runSampledCutoff (sharedSourceCutoff 256)
        (sharedOnlineTotalProgram 256 (sharedOfflineFrame setup.2) selected.1.1
          (Shared.wireCircuit.function scalar selected.1.1)) selected.2) fun encoded =>
          runSampledCutoff (fun request => sharedSourceCutoff 256 (.inr request))
            (sharedWireSourceDecide adversary parameter auxiliary setup.2 selected.1 encoded.1) encoded.2)
      Prod.fst)
  simp only [PMF.map_comp, Function.comp_def] at moved
  simp only [cutoff_map_next] at moved
  exact moved.symm

/-- The exact online implementation closes the complete actual-machine game identity. -/
theorem compiledIdealGame_finiteSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (online : SharedOnlineJoint) (implemented : CompiledOnlineCouplingLaw online)
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 101) :
    GarbledCircuit.SimulatorProtocol.idealGame Shared.packedCircuit Wire.encoding 8887896
      (compiledMachine 256) adversary parameter scalar auxiliary =
      sharedWireFiniteDecision adversary parameter scalar auxiliary :=
  (compiledAdaptiveDecision_machine online implemented adversary parameter scalar auxiliary small).symm.trans
    (compiledAdaptiveDecision_source online implemented adversary parameter scalar auxiliary small)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
