import Proof.Privacy.Source.Invalid.InvalidRestRefresh
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 4096 in
/-- The refreshed event uses direct Enc and hash arguments. -/
theorem invalidRestEventMass_refreshed_normalized [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Nonempty InputMacKey] [Nonempty FullCircuitSource] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)]
    [Fintype EncPRF.HashOracle] [Fintype (PermutationOracle EncPRF.PermutationIndex Block)]
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (rest : GarblingSourceRest) :
    (∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
      (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        invalidRestEventMass scalar table input key reference before after
          {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}) =
    ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
      if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) then
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
            (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
              (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
                (invalidTagGoodEvent {rest with encPRFOracle := enc, hashOracle := hash}
                  (outputKeys construction scalar rest.reference.offsets) table input key
                  {sourcePrefixReference reference rest with encOracle := enc, hashOracle := hash}
                  before after tag) else 0 := by
  have law := invalidRestEventMass_refreshed scalar table input key reference before after rest
  dsimp only at law ⊢
  exact law

end
end Kriterion.ArgoMAC.Security
