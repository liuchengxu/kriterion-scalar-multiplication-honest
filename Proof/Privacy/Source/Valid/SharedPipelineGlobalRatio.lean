import Proof.Privacy.Source.SharedRetainedPipelineRatio
import Proof.Privacy.Source.SharedRealSourceLower

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineGlobalGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription PMF.uniformOfFintype

/-- These commands use the actual retained source and both linked input MACs. -/
def sharedRetainedPipelineCommands [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource) : List FixedCommand :=
  let pointKey := EncPRF.transformKey rest.encPRFOracle
    (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key
  let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness) input (retainedFullSource rest tag)
  scheduleCommands (pipelineGateSchedule sample.curveRequest sample.pointRequests input
    (key.encodeAffine input) (pointKey.encodeAffine input))

/-- The guard keeps complete tags, the public table, good point rows, and a fresh schedule. -/
def SharedPipelineTagGood [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (tag : FullCircuitSource) : Prop :=
  let retained := SharedRetained.retainedSourceContext rest keys input tag key
  FullSourceComplete tag.1 ∧ retainedFullTable rest keys tag = table ∧
    ¬ pointBranchCollision retained.1.visible.2 retained.1.rows retained.1.input retained.1.targets retained.2.2 ∧
    FreshRecordSchedule state.fixedTranscript
      (Shared.Simulator.commandRecords (sharedRetainedPipelineCommands rest keys input key tag))

/-- This mass includes the source ratio loss exactly once. -/
def sharedPipelineTagLowerMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ENNReal :=
  (1 - ((54690772 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
    ((PMF.uniformOfFintype FullCircuitSource) tag * Shared.Simulator.transcriptMass state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1}
          (sharedRetainedPipelineCommands rest keys input key tag))).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries})

/-- The guarded full-pipeline sum stays below the actual retained public event. -/
theorem sharedPipelineGoodTag_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript)
    (budget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    (∑' tag : FullCircuitSource,
      if SharedPipelineTagGood rest keys table input key state tag then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          sharedPipelineTagLowerMass rest keys input key tag state queries else 0) ≤
      sharedRetainedRealPublicMass rest keys table input (key.encodeAffine input) transcript := by
  apply le_trans _ (sharedRetainedRealSource_fullTag_sum_le rest keys table input (key.encodeAffine input) transcript)
  apply ENNReal.tsum_le_tsum
  intro tag
  by_cases good : SharedPipelineTagGood rest keys table input key state tag
  · rw [if_pos good, if_pos ⟨good.1, good.2.1⟩]
    apply mul_le_mul_right
    exact sharedRetainedPipelineSource_ratio rest keys input tag good.1 key state queries
      transcript fixed reference nonfixed good.2.2.1 budget good.2.2.2
  · rw [if_neg good]
    exact bot_le

/-- The guarded global pipeline sum stays below the actual shared public event. -/
def sharedPipelineGoodSource_global_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (budget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle state.fixedTranscript)] := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  have localBound (rest : GarblingSourceRest) :
      (if SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript then
        ∑' tag : FullCircuitSource,
          if SharedPipelineTagGood rest (outputKeys rest) table input key state tag then
            (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
              sharedPipelineTagLowerMass rest (outputKeys rest) input key tag state queries else 0
        else 0) ≤
      sharedRetainedRealPublicMass rest (outputKeys rest) table input (key.encodeAffine input) transcript := by
    split
    · exact sharedPipelineGoodTag_sum_le rest (outputKeys rest) table input key state queries
        transcript fixed reference ‹_› budget
    · exact bot_le
  have first := ENNReal.tsum_le_tsum (fun rest : GarblingSourceRest =>
    mul_le_mul_right (localBound rest) ((PMF.uniformOfFintype GarblingSourceRest) rest))
  rw [← sharedRealTapePublicMass_split witness parameter outputKeys table input (key.encodeAffine input) transcript] at first
  exact first

end
end Kriterion.ArgoMAC.Security
