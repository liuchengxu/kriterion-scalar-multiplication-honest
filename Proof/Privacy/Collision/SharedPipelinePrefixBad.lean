import Proof.Privacy.Collision.SharedFullSourceBad
import Proof.Privacy.Source.Valid.SharedPipelinePrefixMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble retainedFullTable
  circuitMaskSourceTable sharedRetainedPipelineCommands

/-- The complete tag guard is the direct source guard with the exact recorded history. -/
theorem sharedPipelineTagGood_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (input : AffineInput) (history : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler
      (sharedInitialSourceOracle ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩) history) :
    SharedPipelineTagGood rest keys (retainedFullTable rest keys tag) input sample.2
      (transcriptFinalState idealOracleHandler
        (sharedInitialSourceOracle ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩)
        history) tag ↔
      FullSourceComplete tag.1 ∧ ¬ sharedSourcePrefixBad rest.oracleCoin
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
        (rowsForOutputKeys keys rest.algebraic.point.pointRandomness) input (retainedFullSource rest tag)
        sample.2 (sharedFixedTranscriptRecords history) := by
  have recorded := sharedIdealTranscriptFinal_fixedHistory _ _ compatible
  change _ = (sharedFixedTranscriptRecords history).reverse ++ [] at recorded
  rw [List.append_nil] at recorded
  have fresh := sharedFreshRecordSchedule_history (sharedFixedTranscriptRecords history).reverse
    (sharedFixedTranscriptRecords history)
    (Shared.Simulator.commandRecords (sharedRetainedPipelineCommands rest keys input sample.2 tag))
    (fun _ => List.mem_reverse)
  unfold SharedPipelineTagGood sharedSourcePrefixBad
  dsimp only
  rw [recorded, fresh, sharedSourcePipelineRecords_retained,
    sharedSourcePointCollision_retained rest keys input tag sample.2]
  simp only [true_and, not_or, not_not]

/-- The actual prefix failure uses the retained source and the same complete hash tag. -/
theorem sharedFullPipelinePrefixBad_source [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField) (tape : Shared.Randomness) (tag : FullCircuitSource)
    (selected : AffineInput × (State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (compatible : OracleTranscriptCompatible idealOracleHandler
      (sharedInitialSourceOracle (maskRetainedTape tape.val).2.2.2) selected.2.2.2) :
    sharedFullPipelinePrefixBad scalar (tape, tag, selected) ↔
      ¬ FullSourceComplete tag.1 ∨
        sharedSourcePrefixBad
          ⟨tape.val.fixedKeyOracle, tape.val.encPRFOracle, tape.val.hashOracle⟩
          (maskRetainedTape tape.val).2.2.1.1 (maskRetainedTape tape.val).2.2.1.2.value
          (retainedSourceRows scalar (maskRetainedTape tape.val)) selected.1
          (decodeFullSource (tag.1, sharedCircuitHashRest tape.val tag.2)) tape.val.inputMacKey
          (sharedFixedTranscriptRecords selected.2.2.2) := by
  obtain ⟨⟨sample, rest⟩, rfl⟩ := sharedGarblingOracleKeyEquiv.symm.surjective tape
  rw [sharedFullPipelinePrefixBad_oracleKey]
  rw [maskRetainedTape_sharedOracleKey_data] at compatible
  rw [sharedPipelineTagGood_source rest _ sample tag selected.1 selected.2.2.2 compatible]
  rw [retainedSourceRows_sharedOracleKey, sharedCircuitHashRest_sharedOracleKey]
  simp only [not_and_or, not_not]
  rfl

end
end Kriterion.ArgoMAC.Security
