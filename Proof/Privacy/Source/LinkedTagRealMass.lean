import Proof.Privacy.Source.LinkedTagKeyMass
import Proof.Privacy.Source.RealSourceLower

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  instFintypeEncQueryDomainOfBlock
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This order keeps the selected MAC and the complete actual tag event. -/
theorem actualLinkedTagKeyMass_reorder [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (tag : FullCircuitSource) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys rest.algebraic.point.pointRandomness
        rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
        rest.algebraic.field.curveMask rest.reference (retainedFullSource rest tag) tag.1
        (inputSelectedLabelBit input) (inputMacCoordinateEquiv mac) transcript) =
    ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
      (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
        {sample | sample.2.encodeAffine input = mac ∧
          actualFullCircuitSource outputKeys rest.algebraic.point.pointRandomness
            rest.algebraic.field.bridgeKey rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
            rest.algebraic.field.curveMask sample.1 nonfixed.1 nonfixed.2 sample.2 = tag ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            (garblingOracleKeyEquiv.symm (sample,
              {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2})) transcript} := by
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
  apply tsum_congr
  intro nonfixed
  apply congrArg ((PMF.uniformOfFintype
    ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed * ·)
  rw [PMF.toOuterMeasure_map_apply]
  apply congrArg (PMF.toOuterMeasure _)
  ext sample
  simp only [Set.mem_preimage, actualLinkedTagKeyEvent, Set.mem_setOf_eq,
    selectedKeyLabels_public_iff, retainedFullSource_ciphertexts, Prod.mk.eta,
    sourceRest_transcriptCompatible]
  rfl

end
end Kriterion.ArgoMAC.Security
