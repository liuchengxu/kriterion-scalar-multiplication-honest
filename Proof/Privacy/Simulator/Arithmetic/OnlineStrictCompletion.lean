import Proof.Privacy.Simulator.Arithmetic.OnlineLazyMemory
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingSourceJoint
import Proof.Privacy.Source.StrictSourceSampling
namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.OperationalOracle
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] onlineSamplingCoin onlineSamplingMemory onlinePreparedMemory eagerEncLinkSamples Shared.Simulator.commands strictCommands
set_option backward.isDefEq.respectTransparency false in
/-- Finite private sampling and fixed-L linking have the exact strict source decision law. -/
theorem onlineStrictCompletion {budget : Nat} [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (state : Shared.Simulator.OracleState)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (matching : HistoryMatches oracle state.fixedTranscript) (initial : state.bad = false)
    (program : OracleProgram sharedRealOracleSpec Bool budget) :
    (publicCompletion oracle).bind (fun complete =>
      (online.total 256).law.bind fun sample =>
        let next := sharedProgramSelectedGateView
          {state with fixedOracle := complete.1, encOracle := complete.2.1, hashOracle := complete.2.2}
          input (coin.2.1.encodeAffine input)
          ((sharedOfflineFrame coin).selectedCurve input,
            some ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2))
        if next.bad then PMF.pure false else (program.run idealOracleHandler next).map Prod.fst) =
    (onlineSamplingMemory 256 (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).bind
      (fun sampled =>
        let sample := onlineSamplingCoin 256 (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
        (lazyEncLinkSamples (onlinePreparedMemory sampled.1 output sample) oracle).bind fun linked =>
          match strictCommands linked.2
            ((scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
              ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
              input (coin.2.1.encodeAffine input) (encLinkOutputMac linked.1.1 onlineLinkedBase))).map sharedCommand) with
          | none => PMF.pure false
          | some updated => (LazyOracle.run program updated).map Prod.fst) := by
  let base := onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))
  rw [PMF.bind_comm, ← onlineSamplingCoin_source 256 base, PMF.bind_map]
  apply PMF.bind_congr
  intro sampled supported
  let sample := onlineSamplingCoin 256 base sampled
  let commands := fun result : Memory × Nat × Fin 7468 =>
    scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
      ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
      input (coin.2.1.encodeAffine input) (encLinkOutputMac result.1 onlineLinkedBase))
  have law := encLinkSamples_strict_postquery (onlinePreparedMemory sampled.1 output sample) state oracle
    commands (fun _ => program) matching initial
  apply Eq.trans _ law
  apply PMF.bind_congr
  intro complete member
  have mac := eagerOnline_mac memory input output coin stored sampled supported complete
  simp only [sharedProgramSelectedGateView, Shared.Simulator.program, linkedPipelineGateSchedule,
    linkedPointInputMac, sharedOfflineFrame_curveResult, commands]
  rw [mac]
end
end Kriterion.ArgoMAC.ArithmeticSimulator
