import Proof.Privacy.Source.StrictWirePrivacy
import Proof.Privacy.Simulator.Arithmetic.CompiledSetupJoint
import Proof.Privacy.Simulator.StrictOracleLaw
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyDecision

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security
noncomputable section

/-- The supported online law closes the complete fixed-oracle experiment. -/
theorem lazyCompiledIdealGame_finiteSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (online : ∀ memory coin, (memory, coin) ∈ (lazySetupJoint parameter).support →
      lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary memory
        (publicSourceTable coin.1) LazyOracle.empty =
      (OperationalOracle.publicCompletion
        (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
        sharedStrictFrameDecision (SimulatorSampling.online.total 256).law ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
          parameter scalar auxiliary (Shared.Simulator.initialState coin oracle)) :
    GarbledCircuit.LazySimulatorProtocol.idealGame Shared.packedProgramCircuit Wire.encoding 8887896
      lazyCompiledMachine adversary parameter scalar auxiliary =
    sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
      (SimulatorSampling.online.total 256).law ((sharedWireAdversary adversary).rebase Pipeline.Table.pack) parameter scalar auxiliary := by
  rw [lazyParsedGame_phases, lazySetupJoint_parsed, PMF.bind_map]
  dsimp only [Function.comp_def]
  have law : (lazySetupJoint parameter).bind (fun setup =>
      lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary setup.1
        (publicSourceTable setup.2.1) LazyOracle.empty) =
    (lazySetupJoint parameter).bind (fun setup =>
      (OperationalOracle.publicCompletion
        (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracle =>
        sharedStrictFrameDecision (SimulatorSampling.online.total 256).law ((sharedWireAdversary adversary).rebase Pipeline.Table.pack)
          parameter scalar auxiliary (Shared.Simulator.initialState setup.2 oracle)) := by
    apply ThreePhase.bind_eq_on_support
    intro setup member
    exact online setup.1 setup.2 member
  rw [law]
  unfold sharedStrictSourceDecision
  rw [← lazySetupJoint_source parameter, PMF.bind_map]
  rfl

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.OperationalOracle
noncomputable section

/-- The choose phase preserves the fixed-oracle completion law for every continuation. -/
theorem lazyChoose_completion {Result : Type} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget)
    (state : Shared.Simulator.OracleState)
    (lazy : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (next : Result → LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex → PMF Bool)
    (observe : Result → PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex →
      List (PermutationRecord Shared.FixedKeyIndex Block) → PMF Bool)
    (matching : HistoryMatches lazy state.fixedTranscript)
    (continuation : ∀ value updated history, HistoryMatches updated history →
      next value updated = (publicCompletion updated).bind (fun oracle => observe value oracle history)) :
    (LazyOracle.run program lazy).bind (fun result => next result.1 result.2) =
      (publicCompletion lazy).bind (fun oracle =>
        (program.run idealOracleHandler
          {state with fixedOracle := oracle.1, encOracle := oracle.2.1, hashOracle := oracle.2.2}).bind
          (fun result => observe result.1
            (result.2.fixedOracle, result.2.encOracle, result.2.hashOracle) result.2.fixedTranscript)) := by
  have completed := congrArg (fun distribution => distribution.bind
    (fun result => observe result.1 result.2.1 result.2.2))
    (shared_public_completion program state lazy)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at completed
  rw [completed]
  rw [← tracked_run_erase program (lazy, state.fixedTranscript), PMF.bind_map]
  apply ThreePhase.bind_eq_on_support
  intro result member
  exact continuation result.1 result.2.1 result.2.2
    (history_run program (lazy, state.fixedTranscript) matching result member)

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security

/-- Public queries preserve the source's abort flag. -/
theorem sharedPublicRun_bad {Result : Type} {budget : Nat}
    (program : OracleProgram sharedRealOracleSpec Result budget) (state : Shared.Simulator.OracleState)
    (result : Result × Shared.Simulator.OracleState)
    (member : result ∈ (program.run idealOracleHandler state).support) : result.2.bad = state.bad :=
  ThreePhase.run_preserves idealOracleHandler (fun current : Shared.Simulator.OracleState => current.bad)
    (by intro query current; cases query <;> rfl) program state result member

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.OperationalOracle
noncomputable section
set_option maxRecDepth 4096

set_option backward.isDefEq.respectTransparency false in
/-- The choose phase keeps only the oracle fields that affect the strict decision. -/
theorem lazyChosenDecision_completion [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (memory : Memory) (coin : SimulatorSampling.OfflineCoin)
    (online : ∀ (selected : AffineInput × adversary.State) updated history, HistoryMatches updated history →
      ((lazyParsedOnline lazyCompiledMachine memory selected.1
        (Shared.packedProgramCircuit.function scalar selected.1) updated).bind fun encoded => match encoded with
        | none => PMF.pure false
        | some encoded => (LazyOracle.run
            (adversary.decide parameter (publicSourceTable coin.1) encoded.1 auxiliary selected.2) encoded.2).map Prod.fst) =
      (publicCompletion updated).bind fun complete =>
        (SimulatorSampling.online.total 256).law.bind fun random =>
          let next := sharedProgramSelectedGateView
            {(sharedOfflineFrame coin).oracle with
              fixedOracle := complete.1
              encOracle := complete.2.1
              hashOracle := complete.2.2
              fixedTranscript := history}
            selected.1 (coin.2.1.encodeAffine selected.1)
            ((sharedOfflineFrame coin).selectedCurve selected.1,
              (checkedScalarMultiplication scalar.value selected.1).map fun point =>
                (sharedOfflineFrame coin).selectedPoints selected.1 point (Vector.ofFn random.1) random.2)
          if next.bad then PMF.pure false else
            ((adversary.decide parameter (publicSourceTable coin.1)
              (Lamport.selectedLabels (coin.2.1.encodeAffine selected.1)) auxiliary selected.2).run
                idealOracleHandler next).map Prod.fst) :
    lazyChosenDecision lazyCompiledMachine adversary parameter scalar auxiliary memory
      (publicSourceTable coin.1) LazyOracle.empty =
      (publicCompletion (LazyOracle.empty : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)).bind
        fun complete => sharedStrictFrameDecision (SimulatorSampling.online.total 256).law
          ((sharedWireAdversary adversary).rebase Pipeline.Table.pack) parameter scalar auxiliary (Shared.Simulator.initialState coin complete) := by
  have completed := lazyChoose_completion (adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary)
    (sharedOfflineFrame coin).oracle LazyOracle.empty _ _ history_empty online
  refine Eq.trans ?_ (completed.trans ?_)
  · unfold lazyChosenDecision
    apply ThreePhase.bind_eq_on_support
    intro selected _
    apply ThreePhase.bind_eq_on_support
    intro encoded _
    cases encoded <;> rfl
  · apply ThreePhase.bind_eq_on_support
    intro complete _
    unfold sharedStrictFrameDecision
    change ((adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary).run idealOracleHandler
      (Shared.Simulator.initialState coin complete).oracle).bind _ =
      ((adversary.chooseInput parameter (publicSourceTable coin.1) auxiliary).run idealOracleHandler
      (Shared.Simulator.initialState coin complete).oracle).bind _
    apply ThreePhase.bind_eq_on_support
    intro selected member
    apply ThreePhase.bind_eq_on_support
    intro random _
    apply sharedStrictViewDecision_congr
    · rfl
    · rfl
    · rfl
    · rfl
    · exact (sharedPublicRun_bad _ _ selected member).symm

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.OperationalOracle
noncomputable section

/-- The actual closed simulator has the complete finite strict-source decision law. -/
theorem lazyCompiledIdealGame_eqStrict [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable GarbledCircuit.LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    GarbledCircuit.LazySimulatorProtocol.idealGame Shared.packedProgramCircuit Wire.encoding 8887896
      lazyCompiledMachine adversary parameter scalar auxiliary =
    sharedStrictSourceDecision (SimulatorSampling.offline.total 256).law
      (SimulatorSampling.online.total 256).law ((sharedWireAdversary adversary).rebase Pipeline.Table.pack) parameter scalar auxiliary := by
  apply lazyCompiledIdealGame_finiteSource
  intro memory coin member
  apply lazyChosenDecision_completion
  intro selected updated history matching
  exact lazyCompiledOnline_decision memory selected.1 (Shared.packedProgramCircuit.function scalar selected.1)
    coin (lazySetupJoint_words parameter memory coin member)
    {(sharedOfflineFrame coin).oracle with fixedTranscript := history} updated matching rfl
    (fun labels => adversary.decide parameter (publicSourceTable coin.1) labels auxiliary selected.2)

/-- The closed simulator proves the public privacy obligation without hardness axioms. -/
theorem lazyCompiledAdaptivePrivacy [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Shared.PrivateCoins] (witness : Shared.Randomness) :
    GarbledCircuit.OracleAdaptivePrivacy Shared.packedProgramCircuit Wire.encoding 8887896
      (uniformRandomTape Shared.PrivateCoins (Shared.privateCoins witness))
      (fun parameter scalar random => (Shared.packedGarbleProgram parameter scalar random).toOracleProgram) :=
  sharedStrictOraclePrivacy witness lazyCompiledMachine
    (fun adversary parameter scalar => lazyCompiledIdealGame_eqStrict adversary parameter scalar ())

end
end Kriterion.ArgoMAC.ArithmeticSimulator
