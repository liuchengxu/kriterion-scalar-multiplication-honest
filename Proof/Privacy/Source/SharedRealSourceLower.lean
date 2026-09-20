import Proof.Privacy.Source.SharedRealSourceSum
import Proof.Privacy.Source.RealSourceLower

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
local instance sharedPublicSourceKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance sharedPublicSourceKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

set_option maxRecDepth 4096 in
/-- Every complete tag has the exact actual real source mass. -/
theorem sharedRetainedFullSource_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
          rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
          rest.algebraic.field.curveMask (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2 = tag ∧
        OracleTranscriptCompatible sharedRealOracleHandler
          (sharedGarblingOracleKeyEquiv.symm (sample, rest)) transcript} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        sharedLinkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input mac transcript := by
  have mass := sharedRetainedRealSource_mass rest outputKeys (retainedFullSource rest tag) tag.1
    (retainedFullSource_randomizers rest tag) (retainedFullSource_residues rest tag complete)
    input mac transcript
  simpa only [retainedFullSource_ciphertexts, Prod.mk.eta] using mass

/-- This event keeps the entire actual table, selected MAC, and oracle transcript. -/
def sharedRetainedRealPublicMass [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
    {sample | Pipeline.garble outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask rest.algebraic.field.curveR1
      rest.algebraic.field.curveR2 (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2 = table ∧
      sample.2.encodeAffine input = mac ∧ OracleTranscriptCompatible sharedRealOracleHandler
        (sharedGarblingOracleKeyEquiv.symm (sample, rest)) transcript}

set_option maxRecDepth 4096 in
/-- The actual public event splits over the retained tape without a source assumption. -/
theorem sharedRealTapePublicMass_split [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (outputKeys (sharedGarblingOracleKeyEquiv randomness).2) randomness.val.pointRandomness
        randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1 randomness.val.curveR2
        randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle randomness.val.inputMacKey = table ∧
      randomness.val.inputMacKey.encodeAffine input = mac ∧
      OracleTranscriptCompatible sharedRealOracleHandler randomness transcript} =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      sharedRetainedRealPublicMass rest (outputKeys rest) table input mac transcript := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedRandomTape_oracleKey, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  apply congrArg ((PMF.uniformOfFintype GarblingSourceRest) rest * ·)
  simp only [sharedRetainedRealPublicMass, Equiv.apply_symm_apply]
  rfl

set_option maxRecDepth 4096 in
/-- The complete full-tag sum is below the actual public transcript event. -/
theorem sharedRetainedRealSource_fullTag_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (∑' tag : FullCircuitSource,
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
          sharedLinkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input mac transcript
      else 0) ≤ sharedRetainedRealPublicMass rest outputKeys table input mac transcript := by
  let samples := PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
  let tagMap := fun sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey =>
    actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      rest.algebraic.field.curveMask (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2
  let event := fun sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey =>
    Pipeline.garble outputKeys rest.algebraic.point.pointRandomness rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      (Shared.expandOracle sample.1) rest.encPRFOracle rest.hashOracle sample.2 = table ∧
      sample.2.encodeAffine input = mac ∧ OracleTranscriptCompatible sharedRealOracleHandler
        (sharedGarblingOracleKeyEquiv.symm (sample, rest)) transcript
  let kept := fun tag : FullCircuitSource =>
    FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table
  refine le_trans (ENNReal.tsum_le_tsum fun tag => ?_)
    (tagFiberMass_restricted_le samples tagMap event kept)
  by_cases retain : kept tag
  · rw [if_pos retain, if_pos retain]
    rw [← sharedRetainedFullSource_mass rest outputKeys tag retain.1 input mac transcript]
    apply MeasureTheory.measure_mono
    intro sample member
    exact ⟨member.2.1, (retainedFullSource_table rest outputKeys tag retain.1 (Shared.expandOracle sample.1, sample.2) member.2.1).trans retain.2,
      member.1, member.2.2⟩
  · rw [if_neg retain, if_neg retain]


set_option maxRecDepth 4096 in
/-- The complete shared source-tag sum is below the actual public event on the full tape. -/
theorem sharedRealSource_fullTag_global_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Shared.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource,
        if FullSourceComplete tag.1 ∧ retainedFullTable rest (outputKeys rest) tag = table then
          (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
            sharedLinkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input mac transcript
        else 0) ≤
    (uniformRandomTape Shared.Randomness witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (outputKeys (sharedGarblingOracleKeyEquiv randomness).2) randomness.val.pointRandomness
        randomness.val.bridgeKey randomness.val.curveMask randomness.val.curveR1 randomness.val.curveR2
        randomness.val.fixedKeyOracle randomness.val.encPRFOracle randomness.val.hashOracle randomness.val.inputMacKey = table ∧
      randomness.val.inputMacKey.encodeAffine input = mac ∧
      OracleTranscriptCompatible sharedRealOracleHandler randomness transcript} := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedRealTapePublicMass_split]
  apply ENNReal.tsum_le_tsum
  intro rest
  exact mul_le_mul_right (sharedRetainedRealSource_fullTag_sum_le rest (outputKeys rest) table input mac transcript) _

end
end Kriterion.ArgoMAC.Security
