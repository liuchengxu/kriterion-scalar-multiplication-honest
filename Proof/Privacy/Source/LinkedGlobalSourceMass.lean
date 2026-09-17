import Proof.Privacy.Source.LinkedTagRealSum
import Proof.Privacy.Source.SourceRestRefresh

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The nonfixed average disappears when the output keys ignore the refreshed functions. -/
theorem realPublicMass_refresh [Fintype Block] [Nonempty GarblingSourceRest]
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        retainedRealPublicMass {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}
          (outputKeys rest) table input mac history) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      retainedRealPublicMass rest (outputKeys rest) table input mac history := by
  have law := sourceRest_nonfixed_refresh
    (fun rest => retainedRealPublicMass rest (outputKeys rest) table input mac history)
  simpa only [unchanged] using law

set_option maxRecDepth 4096 in
/-- The complete linked tag sum is below the full actual public source event. -/
def linkedGlobalSourceMass_real_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (witness : Garbling.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (unchanged : ∀ rest enc hash,
      outputKeys {rest with encPRFOracle := enc, hashOracle := hash} = outputKeys rest)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :=
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  let bound := ENNReal.tsum_le_tsum (fun rest : GarblingSourceRest =>
    mul_le_mul_right (retainedLinkedTagMass_density_sum_le rest (outputKeys rest) table input mac history)
      ((PMF.uniformOfFintype GarblingSourceRest) rest))
  bound.trans_eq ((realPublicMass_refresh outputKeys unchanged table input mac history).trans
    (realTapePublicMass_split witness parameter outputKeys table input mac history).symm)

end
end Kriterion.ArgoMAC.Security
