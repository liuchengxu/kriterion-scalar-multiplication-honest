import Proof.Privacy.Source.Invalid.InvalidGlobalSourceMass
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
attribute [local instance] instNonemptyInputMacKey_proof_8

/-- This function gives the actual output keys of a retained source. -/
def actualSourceOutputKeys (scalar : ScalarField) (rest : GarblingSourceRest) : OutputKeys :=
  outputKeys construction scalar rest.reference.offsets

set_option maxRecDepth 4096 in
/-- The global invalid count uses the named actual output-key function. -/
theorem invalidRestEventMass_global_normalized [FieldCertificate] [GroupCertificate] [Fintype Block]
    [Fintype FullCircuitSource] [Nonempty FullCircuitSource]
    (sourceWitness nonfixedWitness : Garbling.Randomness) (scalar : ScalarField)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible nonfixedWitness (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv sourceWitness).2⟩
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        invalidRestEventMass scalar table input key reference before after rest) ≤
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        if FullSourceComplete tag.1 ∧ retainedFullTable rest (actualSourceOutputKeys scalar rest) tag = table then
          (fullSourceTagDensity tag)⁻¹ * retainedLinkedTagMass rest (actualSourceOutputKeys scalar rest)
            tag input (key.encodeAffine input) (before ++ after) else 0 := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv sourceWitness).2⟩
  have law := invalidRestEventMass_global_le sourceWitness nonfixedWitness scalar table input key reference
    before after invalid compatible nonfixed budget small bounded
  dsimp only [actualSourceOutputKeys] at law ⊢
  exact law

set_option maxRecDepth 4096 in
/-- The complete invalid event sum is bounded by the actual real public source. -/
def invalidRestEventMass_real_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (sourceWitness nonfixedWitness : Garbling.Randomness) (parameter : Nat) (scalar : ScalarField)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible nonfixedWitness (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) := by
  have lower := invalidRestEventMass_global_normalized sourceWitness nonfixedWitness scalar table input key reference
    before after invalid compatible nonfixed budget small bounded
  have upper := linkedGlobalSourceMass_real_le sourceWitness parameter
      (actualSourceOutputKeys scalar) (fun _ _ _ => rfl)
      table input (key.encodeAffine input) (before ++ after)
  exact lower.trans upper

end
end Kriterion.ArgoMAC.Security
