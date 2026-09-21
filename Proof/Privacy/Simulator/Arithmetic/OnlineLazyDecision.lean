import Proof.Privacy.Simulator.Arithmetic.OnlineLazyGateSource
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyNullSource
import Proof.Privacy.Simulator.Arithmetic.OnlineStrictCompletion
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyExecution
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineProtocol
namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.OperationalOracle
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
attribute [local irreducible] onlineSamplingCoin onlineSamplingMemory onlinePreparedMemory lazyOnlineValidGateResult

/-- The decision parser rejects missing machine output. -/
def lazyResultDecision {budget : Nat}
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget)
    (result : Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat)) : PMF Bool :=
  match result.bind (fun result => (GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.bits 3)).map
    (fun labels => (labels, result.2.1))) with
  | none => PMF.pure false
  | some encoded => (LazyOracle.run (decide encoded.1) encoded.2).map Prod.fst

/-- The private charge does not change the parsed decision. -/
theorem lazyResultDecision_cost {budget : Nat}
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget)
    (result : Option (Memory × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex × Nat))
    (charge : Nat → Nat) :
    lazyResultDecision decide (result.map (fun value => (value.1, value.2.1, charge value.2.2))) =
      lazyResultDecision decide result := by
  cases result <;> rfl

/-- A valid gate result gives the exact strict source decision. -/
theorem lazyOnlineValidGateResult_decision {budget : Nat} [FieldCertificate] [GroupCertificate]
    {coin : OfflineCoin} {input : AffineInput} {output : Point}
    {sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)} {mac : InputMac} {memory : Memory}
    (ready : LazyOnlineGateData coin input output sample mac memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget) :
    lazyResultDecision decide (lazyOnlineValidGateResult memory oracle) =
      match strictCommands oracle
        ((scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
          ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
          input ((sharedOfflineFrame coin).labels input).inputMac mac)).map sharedCommand) with
      | none => PMF.pure false
      | some updated => (LazyOracle.run (decide (Lamport.selectedLabels (coin.2.1.encodeAffine input))) updated).map Prod.fst := by
  unfold lazyResultDecision
  rw [lazyOnlineValidGateResult_parsed ready oracle]
  cases strictCommands oracle
    ((scheduleCommands (pipelineGateSchedule ((sharedOfflineFrame coin).selectedCurve input)
      ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
      input ((sharedOfflineFrame coin).labels input).inputMac mac)).map sharedCommand) <;> rfl

/-- The valid machine body has the exact completed strict source decision law. -/
theorem lazyOnlineValidBodyResult_decision {budget : Nat} [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (output : Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) (state : Shared.Simulator.OracleState)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (matching : HistoryMatches oracle state.fixedTranscript) (initial : state.bad = false)
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget) :
    (publicCompletion oracle).bind (fun complete =>
      (online.total 256).law.bind fun sample =>
        let next := sharedProgramSelectedGateView
          {state with fixedOracle := complete.1, encOracle := complete.2.1, hashOracle := complete.2.2}
          input (coin.2.1.encodeAffine input)
          ((sharedOfflineFrame coin).selectedCurve input,
            some ((sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2))
        if next.bad then PMF.pure false else
          ((decide (Lamport.selectedLabels (coin.2.1.encodeAffine input))).run idealOracleHandler next).map Prod.fst) =
    (lazyOnlineValidBodyResult (onlineTagMemory (onlineCurveMemory memory input (some output) [])) output oracle).bind
      (lazyResultDecision decide) := by
  rw [onlineStrictCompletion memory input output coin stored state oracle matching initial]
  simp only [lazyOnlineValidBodyResult, PMF.bind_bind, PMF.pure_bind]
  apply PMF.bind_congr
  intro sampled supported
  apply PMF.bind_congr
  intro linked member
  have cost := lazyResultDecision_cost decide (lazyOnlineValidGateResult linked.1.1 linked.2)
    (fun value => value + linked.1.2.1 + onlinePrepareCost (onlineSamplingCoin 256
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled) + sampled.2 + 1)
  simp only [onlineSampleInitial] at cost
  rw [cost, lazyOnlineValidGateResult_decision
    (lazyOnline_gateData memory input output coin stored empty sampled supported oracle linked member)]
  rfl

/-- The null gate result gives the exact strict source decision. -/
theorem lazyOnlineNullResult_decision {budget : Nat} [FieldCertificate]
    (memory : Memory) (input : AffineInput) (coin : OfflineCoin)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = [])
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget) :
    lazyResultDecision decide (lazyOnlineNullResult memory input [] oracle) =
      match strictCommands oracle
        ((scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
          (coin.2.1.encodeAffine input))).map sharedCommand) with
      | none => PMF.pure false
      | some updated => (LazyOracle.run (decide (Lamport.selectedLabels (coin.2.1.encodeAffine input))) updated).map Prod.fst := by
  unfold lazyResultDecision
  rw [lazyOnlineNullResult_parsed memory input coin oracle stored empty]
  simp only [sharedOfflineFrame_inputMac]
  cases strictCommands oracle ((scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
    (coin.2.1.encodeAffine input))).map sharedCommand) <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Both online branches have the exact completed strict source decision law. -/
theorem lazyOnlineResult_decision {budget : Nat} [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (value : Option Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (empty : memory.bits 3 = []) (state : Shared.Simulator.OracleState)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (matching : HistoryMatches oracle state.fixedTranscript) (initial : state.bad = false)
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget) :
    (publicCompletion oracle).bind (fun complete =>
      (online.total 256).law.bind fun sample =>
        let next := sharedProgramSelectedGateView
          {state with fixedOracle := complete.1, encOracle := complete.2.1, hashOracle := complete.2.2}
          input (coin.2.1.encodeAffine input)
          ((sharedOfflineFrame coin).selectedCurve input,
            value.map fun output => (sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
        if next.bad then PMF.pure false else
          ((decide (Lamport.selectedLabels (coin.2.1.encodeAffine input))).run idealOracleHandler next).map Prod.fst) =
    (lazyOnlineResult memory input value oracle).bind (lazyResultDecision decide) := by
  cases value with
  | none =>
    simp only [Option.map_none, PMF.bind_const, lazyOnlineResult, PMF.pure_bind,
      lazyOnlineNullResult_decision memory input coin oracle stored empty decide]
    exact sharedCommands_strict_postquery (decide (Lamport.selectedLabels (coin.2.1.encodeAffine input)))
      state oracle (scheduleCommands (((sharedOfflineFrame coin).selectedCurve input).schedule input
        (coin.2.1.encodeAffine input))) matching initial
  | some output =>
    have cost (result) := lazyResultDecision_cost decide result
      (fun charge => charge + 3 + onlinePrefixCost (some output))
    simp only [Option.map_some, lazyOnlineResult, lazyOnlineValidResult, PMF.bind_map, Function.comp_def, cost]
    exact lazyOnlineValidBodyResult_decision memory input output coin stored empty state oracle matching initial decide

/-- The actual parsed online phase has the exact completed strict source law. -/
theorem lazyCompiledOnline_decision {budget : Nat} [FieldCertificate] [GroupCertificate]
    (memory : Memory) (input : AffineInput) (value : Option Point) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (state : Shared.Simulator.OracleState)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (matching : HistoryMatches oracle state.fixedTranscript) (initial : state.bad = false)
    (decide : GarbledCircuit.LamportSignature → OracleProgram sharedRealOracleSpec Bool budget) :
    (lazyParsedOnline lazyCompiledMachine memory input value oracle).bind (fun encoded => match encoded with
      | none => PMF.pure false
      | some encoded => (LazyOracle.run (decide encoded.1) encoded.2).map Prod.fst) =
    (publicCompletion oracle).bind (fun complete =>
      (online.total 256).law.bind fun sample =>
        let next := sharedProgramSelectedGateView
          {state with fixedOracle := complete.1, encOracle := complete.2.1, hashOracle := complete.2.2}
          input (coin.2.1.encodeAffine input)
          ((sharedOfflineFrame coin).selectedCurve input,
            value.map fun output => (sharedOfflineFrame coin).selectedPoints input output (Vector.ofFn sample.1) sample.2)
        if next.bad then PMF.pure false else
          ((decide (Lamport.selectedLabels (coin.2.1.encodeAffine input))).run idealOracleHandler next).map Prod.fst) := by
  rw [lazyCompiledMachine_onlineParsed, PMF.bind_map]
  exact (lazyOnlineResult_decision
    (compiledOnlineMemory memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output value))
    input value coin stored (by simp [compiledOnlineMemory]) state oracle matching initial decide).symm

end
end Kriterion.ArgoMAC.ArithmeticSimulator
