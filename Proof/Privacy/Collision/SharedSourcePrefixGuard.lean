import Proof.Privacy.Collision.SharedSourcePointCollision
import Proof.Privacy.Source.Valid.SharedPipelineGlobalRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section
attribute [local irreducible] circuitMaskSampleGarble pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords

/-- The source guard retains the complete selected pipeline schedule. -/
def sharedSourcePipelineRecords (oracle : SimulatorOracleCoin) (bridge mask : BaseField)
    (rows : Rows) (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey) :=
  let pointKey := EncPRF.transformKey oracle.encOracle (EncPRF.whiteningKeys oracle.hashOracle bridge) key
  let sample := circuitMaskSampleGarble bridge mask rows input source
  Shared.Simulator.commandRecords (scheduleCommands (pipelineGateSchedule sample.curveRequest sample.pointRequests
    input (key.encodeAffine input) (pointKey.encodeAffine input)))

/-- The source fails when its point rows collide or its selected schedule is not fresh. -/
def sharedSourcePrefixBad (oracle : SimulatorOracleCoin) (bridge mask : BaseField)
    (rows : Rows) (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) : Prop :=
  sharedSourcePointCollision source ∨ ¬ FreshRecordSchedule history
    (sharedSourcePipelineRecords oracle bridge mask rows input source key)

/-- History membership alone determines schedule freshness. -/
theorem sharedFreshRecordSchedule_history {Index : Type}
    (first second records : List (PermutationRecord Index Block))
    (members : ∀ record, record ∈ first ↔ record ∈ second) :
    FreshRecordSchedule first records ↔ FreshRecordSchedule second records := by
  induction records generalizing first second with
  | nil => rfl
  | cons record rest ih =>
      simp only [FreshRecordSchedule, FreshPermutationPair]
      constructor
      · intro good
        refine ⟨fun prior member same => good.1 prior ((members prior).mpr member) same, ?_⟩
        exact (ih (record :: first) (record :: second) (by intro prior; simp only [List.mem_cons, members])).mp good.2
      · intro good
        refine ⟨fun prior member same => good.1 prior ((members prior).mp member) same, ?_⟩
        exact (ih (record :: first) (record :: second) (by intro prior; simp only [List.mem_cons, members])).mpr good.2

/-- The checked point and prequery flags imply the complete shared source guard. -/
theorem sharedSourcePrefixBad_split_false (oracle : SimulatorOracleCoin) (bridge mask : BaseField)
    (rows : Rows) (sparse : ∀ row, SparseRow (rows.get row)) (input : AffineInput)
    (sample : PublicSample) (key : InputMacKey) (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (pointGood : ¬ retainedSourceBirthday sample rows input)
    (prefixGood : let source := (circuitMaskSampleSplit bridge mask rows input sample).2
      ¬ sharedPrequeryLabelCollision history
        (sharedSourcePrequeryUses oracle bridge source
          (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) history) key) :
    ¬ sharedSourcePrefixBad oracle bridge mask rows input
      (circuitMaskSampleSplit bridge mask rows input sample).2 key history := by
  have sourceEq := reconstructedCircuitSource_eq_split bridge mask rows sparse input sample
  have fresh := sharedReconstructedCircuitSource_schedule_fresh
    { fixedOracle := Shared.restrictOracle oracle.fixedOracle, encOracle := oracle.encOracle,
      hashOracle := oracle.hashOracle, fixedTranscript := history, encTranscript := [], hashTranscript := [],
      commitments := [], linking := none, bad := false }
    oracle bridge mask sample rows input (bridge + mask * (input.x ^ 3 + 3 - input.y ^ 2))
    (fun row => (evaluateRowsCubic rows input).get row) key pointGood
    (by simpa only [sourceEq] using prefixGood)
  rw [sourceEq] at fresh
  intro bad
  rcases bad with pointBad | scheduleBad
  · exact pointGood ((sharedSourcePointCollision_split bridge mask rows sparse input sample).mp pointBad)
  · exact scheduleBad fresh

/-- The retained tag schedule is the exact direct source schedule. -/
theorem sharedSourcePipelineRecords_retained [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : OutputKeys) (input : AffineInput) (key : InputMacKey)
    (tag : FullCircuitSource) :
    sharedSourcePipelineRecords rest.oracleCoin rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask.value (rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
      input (retainedFullSource rest tag) key =
      Shared.Simulator.commandRecords (sharedRetainedPipelineCommands rest keys input key tag) := rfl

end
end Kriterion.ArgoMAC.Security
