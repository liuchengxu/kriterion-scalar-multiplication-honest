/-
This file defines the concrete online ArgoMAC simulator.
-/

import Proof.Privacy.Distribution.ProjectiveDistribution
import Security.AdaptivePrivacy

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This state keeps the hidden public sample and its programmable oracles. -/
structure CircuitSimulatorState where
  oracle : SimulatorState
  curve : CurveGateRequest
  points : PointGateRequests
  inputKey : InputMacKey
  bridgeKey : BaseField

def CircuitSimulatorState.table (state : CircuitSimulatorState) : Pipeline.Table := {
  curve := state.curve.table
  pointMAC := pointGateTable state.points
}

def CircuitSimulatorState.labels (state : CircuitSimulatorState)
    (input : AffineInput) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := state.inputKey.encodeAffine input
}

def CircuitSimulatorState.selectedCurve (state : CircuitSimulatorState)
    (input : AffineInput) : CurveGateRequest :=
  state.curve.retarget input state.bridgeKey

def CircuitSimulatorState.selectedPoints [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    PointGateRequests :=
  retargetPointGateRequests state.points input (outputTargets output free scales)

def CircuitSimulatorState.selectedSchedule [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    List GateDirective :=
  linkedPipelineGateSchedule state.oracle (state.selectedCurve input)
    (state.selectedPoints input output free scales) input (state.labels input).inputMac

/-- This operation programs the selected rows for one requested output. -/
def CircuitSimulatorState.programForOutput [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    CircuitSimulatorState :=
  { state with oracle := programGateSchedule state.oracle (state.selectedSchedule input output free scales) }

/-- The ideal handler updates only the programmable oracle state. -/
def circuitSimulatorOracleHandler :
    OracleHandler Garbling.oracleSpec CircuitSimulatorState
  | query, state =>
      let answered := idealOracleHandler query state.oracle
      (answered.1, { state with oracle := answered.2 })

/-- This simulator samples a public state and programs the online selected path. -/
noncomputable def circuitSimulator [FieldCertificate] [GroupCertificate]
    (stateTape : Nat → Garbling.Topology → PMF CircuitSimulatorState) :
    GarbledCircuit.Simulator AffineInput (Option Point) Pipeline.Table Garbling.Labels
      Garbling.Topology CircuitSimulatorState := by
  classical
  exact {
    simulateGarble := fun parameter topology =>
      (stateTape parameter topology).map fun state => (state.table, state)
    simulateEncode := fun state input output => match output with
      | none =>
          let schedule := (state.selectedCurve input).schedule input (state.labels input).inputMac
          PMF.pure (state.labels input,
            { state with oracle := programGateSchedule state.oracle schedule })
      | some point =>
          (PMF.uniformOfFintype ((Fin 90 → Point) ×
            (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun sample =>
              (state.labels input,
                state.programForOutput input point (Vector.ofFn sample.1) sample.2)
  }

/-- The challenge checks these tables against the ideal handler's answers. -/
def CircuitSimulatorState.view (state : CircuitSimulatorState) : Garbling.EvaluationOracle :=
  (state.oracle.fixedOracle, state.oracle.encOracle, state.oracle.hashOracle)

/-- The fixed-key transcript marks earlier queries. The other tables never change. -/
def SimulatorState.seen (state : SimulatorState) : Garbling.OracleQuery → Prop
  | .fixedForward index input => ∃ record ∈ state.fixedTranscript,
      record.index = index ∧ record.domain = input
  | .fixedInverse index output => ∃ record ∈ state.fixedTranscript,
      record.index = index ∧ record.range = output
  | _ => True

theorem SimulatorState.seen_mono {first second : SimulatorState}
    (records : first.fixedTranscript ⊆ second.fixedTranscript) (query : Garbling.OracleQuery)
    (seen : first.seen query) : second.seen query := by
  cases query <;> simp only [SimulatorState.seen] at *
  all_goals first | trivial | obtain ⟨record, member, equal⟩ := seen; exact ⟨record, records member, equal⟩

/-- Matching retained records force both permutation directions to keep their answers. -/
theorem CircuitSimulatorState.answer_preserved {first second : CircuitSimulatorState}
    (firstValid : SimulatorInvariant first.oracle) (secondValid : SimulatorInvariant second.oracle)
    (records : first.oracle.fixedTranscript ⊆ second.oracle.fixedTranscript)
    (enc : second.oracle.encOracle = first.oracle.encOracle)
    (hash : second.oracle.hashOracle = first.oracle.hashOracle)
    (query : Garbling.OracleQuery) (seen : first.oracle.seen query) :
    publicAnswer second.view query = publicAnswer first.view query := by
  cases query with
  | fixedForward index input =>
      obtain ⟨record, member, rfl, rfl⟩ := seen
      exact (secondValid.1 record (records member)).trans (firstValid.1 record member).symm
  | fixedInverse index output =>
      obtain ⟨record, member, rfl, rfl⟩ := seen
      exact ((Equiv.symm_apply_eq _).mpr (secondValid.1 record (records member)).symm).trans
        ((Equiv.symm_apply_eq _).mpr (firstValid.1 record member).symm).symm
  | encForward index input => simp only [publicAnswer, CircuitSimulatorState.view, enc]; rfl
  | encInverse index output => simp only [publicAnswer, CircuitSimulatorState.view, enc]; rfl
  | hash input => simp [publicAnswer, CircuitSimulatorState.view, hash]

theorem circuitSimulator_oracleSimulation [FieldCertificate] [GroupCertificate]
    (tape : Nat → Garbling.Topology → PMF CircuitSimulatorState)
    (initial : ∀ parameter topology state, state ∈ (tape parameter topology).support →
      SimulatorInvariant state.oracle) :
    GarbledCircuit.OracleSimulation (circuitSimulator tape) circuitSimulatorOracleHandler
      CircuitSimulatorState.view := by
  refine ⟨fun state => SimulatorInvariant state.oracle, fun state query => state.oracle.seen query, ?_, ?_, ?_⟩
  · intro parameter topology result member
    dsimp only [circuitSimulator] at member
    rw [PMF.support_map] at member
    obtain ⟨state, stateMember, rfl⟩ := member
    exact initial parameter topology state stateMember
  · intro query state valid
    refine ⟨by cases query <;> rfl, by cases query <;> rfl,
      idealOracleHandler_preservesInvariant query state.oracle valid, ?_, ?_⟩
    · cases query <;> simp [SimulatorState.seen, circuitSimulatorOracleHandler,
        idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash]
    · intro prior seen
      apply SimulatorState.seen_mono (query := prior) ?_ seen
      cases query <;> simp [circuitSimulatorOracleHandler, idealOracleHandler,
        oracleHandlerFor, recordFixed, recordEnc, recordHash]
  · intro state input output result valid member
    have programmed (schedule : List GateDirective) :
        let next := { state with oracle := programGateSchedule state.oracle schedule }
        SimulatorInvariant next.oracle ∧ ∀ query, state.oracle.seen query →
          next.oracle.seen query ∧ publicAnswer next.view query = publicAnswer state.view query := by
      have nextValid := programGateSchedule_preservesInvariant state.oracle schedule valid
      have records := programGateSchedule_preservesRecords state.oracle schedule
      refine ⟨nextValid, fun query seen => ⟨SimulatorState.seen_mono records query seen, ?_⟩⟩
      exact CircuitSimulatorState.answer_preserved valid nextValid records (by simp) (by simp) query seen
    cases output with
    | none =>
        dsimp only [circuitSimulator] at member
        have equal := (PMF.mem_support_pure_iff _ _).mp member
        subst result
        exact programmed _
    | some point =>
        dsimp only [circuitSimulator] at member
        rw [PMF.support_map] at member
        obtain ⟨sample, _, rfl⟩ := member
        exact programmed _

end Kriterion.ArgoMAC.Security
