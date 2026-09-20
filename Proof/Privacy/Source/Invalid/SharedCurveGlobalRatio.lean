import Proof.Privacy.Source.SharedRetainedCurveRatio
import Proof.Privacy.Source.SharedLinkedGlobalSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveGlobalGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription PMF.uniformOfFintype

/-- These commands program the actual curve branch of a retained source tag. -/
def sharedRetainedCurveCommands [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource) :=
  let rows := FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness
  let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey
    rest.algebraic.field.curveMask.value rows input (retainedFullSource rest tag)
  scheduleCommands (sample.curveRequest.schedule input (key.encodeAffine input))

/-- This guard retains the exact source assumptions for the curve branch. -/
def SharedCurveTagGood [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource) : Prop :=
  let retained := SharedRetained.retainedSourceContext rest keys input tag key
  FullSourceComplete tag.1 ∧ retainedFullTable rest keys tag = table ∧
    rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (sharedLegacyTranscript transcript) ∧
    ¬ pointBranchCollision retained.1.visible.2 retained.1.rows retained.1.input retained.1.targets retained.2.2 ∧
    FreshRecordSchedule state.fixedTranscript
      (Shared.Simulator.commandRecords (sharedRetainedCurveCommands rest keys input key tag))

/-- This mass contains the exact relative losses for one actual curve program. -/
def sharedCurveTagLowerMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) (budget : Nat)
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ENNReal :=
  ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
    encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))) *
    (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      if SharedNonFixedTranscriptCompatible (state.fixedOracle, rest.encPRFOracle, hash) transcript then
        (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
          ((PMF.uniformOfFintype FullCircuitSource) tag *
            Shared.Simulator.transcriptMass state.fixedTranscript *
            ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
              (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1}
                (sharedRetainedCurveCommands rest keys input key tag))).toOuterMeasure
              {next | PermutationTranscriptMatches next.fixedOracle queries}) else 0)

/-- The guarded sum of actual curve programs stays below the refreshed real source. -/
theorem sharedCurveGoodTag_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : transcript.length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    (∑' tag : FullCircuitSource,
      if SharedCurveTagGood rest keys table input key state transcript tag then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          sharedCurveTagLowerMass rest keys input key tag state queries transcript budget else 0) ≤
      sharedRefreshedLinkedSourceMass rest keys table input (key.encodeAffine input) transcript := by
  unfold sharedRefreshedLinkedSourceMass
  apply ENNReal.tsum_le_tsum
  intro tag
  by_cases good : SharedCurveTagGood rest keys table input key state transcript tag
  · rw [if_pos good, if_pos ⟨good.1, good.2.1⟩]
    apply mul_le_mul_right
    exact sharedRetainedCurveSource_linked_ratio rest keys input tag good.1 key state queries
      transcript fixed good.2.2.1 good.2.2.2.1 budget small lengthBound good.2.2.2.2
  · rw [if_neg good]
    exact bot_le

/-- The guarded global curve-program sum stays below the actual shared public event. -/
def sharedCurveGoodSource_global_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : transcript.length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  have first := ENNReal.tsum_le_tsum (fun rest : GarblingSourceRest =>
    mul_le_mul_right (sharedCurveGoodTag_sum_le rest (outputKeys rest) table input key state queries
      transcript fixed budget small lengthBound) ((PMF.uniformOfFintype GarblingSourceRest) rest))
  exact first.trans (sharedLinkedGlobalSourceMass_real_le witness parameter outputKeys unchanged
    table input (key.encodeAffine input) transcript)

end
end Kriterion.ArgoMAC.Security
