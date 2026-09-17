import Proof.Privacy.Source.Valid.ValidSourceRatio
import Proof.Privacy.Source.FullGateSourceMass
import Proof.Privacy.Source.TagFiberMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This source keeps the retained randomizers and the full public tag. -/
def retainedFullSource [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource) : CircuitMaskSample :=
  decodeFullSource (tag.1, sharedCircuitHashRest rest.reference tag.2)

/-- The decoded source keeps the actual field randomizers. -/
theorem retainedFullSource_randomizers [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource) :
    CircuitSourceRandomizers (retainedFullSource rest tag) rest.algebraic.point.pointRandomness
      rest.algebraic.field.curveR1 rest.algebraic.field.curveR2 :=
  sharedCircuitMaskSample_randomizers rest.reference (fun gate => fullSourceHashPair (tag.1 gate)) tag.2

/-- Complete decoding keeps the original full hash tape. -/
theorem retainedFullSource_lifts [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1) :
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv (retainedFullSource rest tag)).1 gate)) = tag.1 :=
  decodeFullSource_lifts (tag.1, sharedCircuitHashRest rest.reference tag.2) complete

/-- Complete decoding keeps each full hash residue. -/
theorem retainedFullSource_residues [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (gate : RawCircuitGate) :
    circuitSourceField (retainedFullSource rest tag) gate = ((tag.1 gate).val : BaseField) := by
  rw [← retainedFullSource_lifts rest tag complete]
  simp only [retainedFullSource, decodeFullSource, Equiv.apply_symm_apply]
  exact sharedCircuitMaskSample_residues rest.reference
    (fun gate => fullSourceHashPair (tag.1 gate)) tag.2 gate

/-- Decoding keeps every ciphertext in the full source tag. -/
theorem retainedFullSource_ciphertexts [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (tag : FullCircuitSource) :
    sourceCiphertexts (retainedFullSource rest tag) = tag.2 := by
  apply circuitMaskTablesEquiv.injective
  rw [sourceCiphertexts, Equiv.apply_symm_apply]
  funext gate
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> rfl

attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

set_option maxRecDepth 4096 in
/-- Every complete tag has the exact actual real source mass. -/
theorem retainedFullSource_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
          rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
          rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2 = tag ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          (garblingOracleKeyEquiv.symm (sample, rest)) transcript} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        linkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input mac transcript := by
  have mass := retainedRealSource_mass rest outputKeys (retainedFullSource rest tag) tag.1
    (retainedFullSource_randomizers rest tag) (retainedFullSource_residues rest tag complete)
    input mac transcript
  simpa only [retainedFullSource_ciphertexts, Prod.mk.eta] using mass

/-- This table uses the actual output keys and retained field randomizers. -/
def retainedFullTable [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) : Pipeline.Table :=
  circuitMaskSourceTable rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    (retainedFullSource rest tag)

/-- The actual tag determines the entire public table on complete fibers. -/
theorem retainedFullSource_table [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (same : actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2 = tag) :
    Pipeline.garble outputKeys rest.algebraic.point.pointRandomness rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      sample.1 rest.encPRFOracle rest.hashOracle sample.2 = retainedFullTable rest outputKeys tag := by
  apply actualFullCircuitSource_table outputKeys rest.algebraic.point.pointRandomness
    rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2
    (retainedFullSource rest tag) tag.1 (retainedFullSource_randomizers rest tag)
    (retainedFullSource_residues rest tag complete)
  simpa only [retainedFullSource_ciphertexts, Prod.mk.eta] using same

/-- This event keeps the entire actual table, selected MAC, and oracle transcript. -/
def retainedRealPublicMass [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
    {sample | Pipeline.garble outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask rest.algebraic.field.curveR1
      rest.algebraic.field.curveR2 sample.1 rest.encPRFOracle rest.hashOracle sample.2 = table ∧
      sample.2.encodeAffine input = mac ∧ OracleTranscriptCompatible Garbling.oracleHandler
        (garblingOracleKeyEquiv.symm (sample, rest)) transcript}

set_option maxRecDepth 4096 in
/-- The actual public event splits over the retained tape without a source assumption. -/
theorem realTapePublicMass_split [Fintype Block]
    (witness : Garbling.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    (randomTape witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (outputKeys (garblingOracleKeyEquiv randomness).2) randomness.pointRandomness
        randomness.bridgeKey randomness.curveMask randomness.curveR1 randomness.curveR2
        randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle randomness.inputMacKey = table ∧
      randomness.inputMacKey.encodeAffine input = mac ∧
      OracleTranscriptCompatible Garbling.oracleHandler randomness transcript} =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      retainedRealPublicMass rest (outputKeys rest) table input mac transcript := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  rw [randomTape_oracleKey, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  apply congrArg ((PMF.uniformOfFintype GarblingSourceRest) rest * ·)
  simp only [retainedRealPublicMass, Equiv.apply_symm_apply]
  rfl

set_option maxRecDepth 4096 in
/-- The complete full-tag sum is below the actual public transcript event. -/
theorem retainedRealSource_fullTag_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' tag : FullCircuitSource,
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
          linkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input mac transcript
      else 0) ≤ retainedRealPublicMass rest outputKeys table input mac transcript := by
  let samples := PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
  let tagMap := fun sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey =>
    actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      rest.algebraic.field.curveMask sample.1 rest.encPRFOracle rest.hashOracle sample.2
  let event := fun sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey =>
    Pipeline.garble outputKeys rest.algebraic.point.pointRandomness rest.algebraic.field.bridgeKey
      rest.algebraic.field.curveMask rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      sample.1 rest.encPRFOracle rest.hashOracle sample.2 = table ∧
      sample.2.encodeAffine input = mac ∧ OracleTranscriptCompatible Garbling.oracleHandler
        (garblingOracleKeyEquiv.symm (sample, rest)) transcript
  let kept := fun tag : FullCircuitSource =>
    FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table
  refine le_trans (ENNReal.tsum_le_tsum fun tag => ?_)
    (tagFiberMass_restricted_le samples tagMap event kept)
  by_cases retain : kept tag
  · rw [if_pos retain, if_pos retain]
    rw [← retainedFullSource_mass rest outputKeys tag retain.1 input mac transcript]
    apply MeasureTheory.measure_mono
    intro sample member
    exact ⟨member.2.1, (retainedFullSource_table rest outputKeys tag retain.1 sample member.2.1).trans retain.2,
      member.1, member.2.2⟩
  · rw [if_neg retain, if_neg retain]

end
end Kriterion.ArgoMAC.Security
