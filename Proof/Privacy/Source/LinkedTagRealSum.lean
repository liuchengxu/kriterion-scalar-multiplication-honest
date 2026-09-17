import Proof.Privacy.Source.LinkedTagRealMass
import Proof.Privacy.Source.NormalizedLinkedCurveRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  instFintypeEncQueryDomainOfBlock bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This mass averages all real oracle functions inside one retained full tag. -/
def retainedLinkedTagMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
    ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
    (actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
      rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
      rest.algebraic.field.curveMask rest.reference (retainedFullSource rest tag) tag.1
      (inputSelectedLabelBit input) (inputMacCoordinateEquiv mac) transcript)

/-- The retained full table does not read the nonfixed oracle functions. -/
theorem retainedFullTable_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys) (tag : FullCircuitSource)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    retainedFullTable {rest with encPRFOracle := enc, hashOracle := hash} outputKeys tag =
      retainedFullTable rest outputKeys tag := rfl

set_option maxRecDepth 2048 in
/-- Each complete linked tag equals the exact nonfixed average of its real hidden-label mass. -/
theorem retainedLinkedTagMass_complete [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    retainedLinkedTagMass rest outputKeys tag input mac transcript =
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        linkedHiddenSourceMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
          (retainedFullSource {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2} tag)
          tag.1 input mac transcript := by
  rw [retainedLinkedTagMass, actualLinkedTagKeyMass_reorder]
  apply tsum_congr
  intro nonfixed
  rw [retainedFullSource_mass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
    outputKeys tag complete input mac transcript]
  exact (mul_assoc _ _ _).symm


set_option maxRecDepth 2048 in
/-- The unweighted linked tag fibers remain below one actual public event. -/
theorem retainedLinkedTagMass_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' tag : FullCircuitSource,
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
        retainedLinkedTagMass rest outputKeys tag input mac transcript else 0) ≤
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        retainedRealPublicMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
          outputKeys table input mac transcript := by
  have ordered :
      (∑' tag : FullCircuitSource,
        if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
          retainedLinkedTagMass rest outputKeys tag input mac transcript else 0) =
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        ∑' tag : FullCircuitSource,
          if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
            (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
            linkedHiddenSourceMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
              (retainedFullSource {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2} tag)
              tag.1 input mac transcript else 0 := by
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro tag
    by_cases retain : FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table
    · rw [if_pos retain, retainedLinkedTagMass_complete rest outputKeys tag retain.1 input mac transcript]
      simp only [if_pos retain, mul_assoc]
    · simp only [if_neg retain, mul_zero, tsum_zero]
  rw [ordered]
  apply ENNReal.tsum_le_tsum
  intro nonfixed
  apply mul_le_mul_right
  have bound := retainedRealSource_fullTag_sum_le
    {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2} outputKeys table input mac transcript
  simp only [retainedFullTable_nonfixed] at bound
  exact bound

private theorem scalar_density_guard (density inverse weight : ℝ≥0∞) (kept : Prop) [Decidable kept]
    (cancel : density * inverse = 1) :
    density * (if kept then inverse * weight else 0) ≤ if kept then weight else 0 := by
  by_cases member : kept
  · rw [if_pos member, if_pos member, ← mul_assoc, cancel, one_mul]
  · rw [if_neg member, if_neg member, mul_zero]

set_option maxRecDepth 2048 in
/-- The normalized full-tag density cancels before the actual source fibers are summed. -/
theorem retainedLinkedTagMass_density_sum_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table then
        (fullSourceTagDensity tag)⁻¹ * retainedLinkedTagMass rest outputKeys tag input mac transcript else 0) ≤
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        retainedRealPublicMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
          outputKeys table input mac transcript := by
  apply le_trans _ (retainedLinkedTagMass_sum_le rest outputKeys table input mac transcript)
  apply ENNReal.tsum_le_tsum
  intro tag
  have same : (PMF.uniformOfFintype FullCircuitSource) tag = fullSourceTagDensity tag := rfl
  have nonzero : (PMF.uniformOfFintype FullCircuitSource) tag ≠ 0 := by
    simp only [PMF.uniformOfFintype_apply, ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top _
  have cancel : (PMF.uniformOfFintype FullCircuitSource) tag * (fullSourceTagDensity tag)⁻¹ = 1 :=
    (congrArg (fun value : ℝ≥0∞ => (PMF.uniformOfFintype FullCircuitSource) tag * value⁻¹) same.symm).trans
      (ENNReal.mul_inv_cancel nonzero (PMF.apply_ne_top _ tag))
  exact scalar_density_guard ((PMF.uniformOfFintype FullCircuitSource) tag)
    ((fullSourceTagDensity tag)⁻¹) (retainedLinkedTagMass rest outputKeys tag input mac transcript)
    (FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table) cancel

end
end Kriterion.ArgoMAC.Security
