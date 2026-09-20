import Proof.Privacy.Transcript.SharedLegacyTranscript

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
local instance sharedHiddenEncKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The shared source uses the same relative EncPRF count at each fixed shared oracle. -/
theorem sharedHiddenEncSource_weighted_mass_ge [Fintype Block] [Fintype BaseField]
    (hidden : BaseField) (source : InputMacKey) (rest : GarblingSourceRest)
    (fixed : PermutationOracle Shared.FixedKeyIndex Block)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (miss : hidden ∉ transcriptHashInputs (sharedLegacyTranscript transcript))
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card
      (EncQueryDomain (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) index) ≤ Fintype.card Block)
    (weight : InputMacKey → ENNReal) :
    (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      if OracleTranscriptCompatible (publicHandler id) (fixed, rest.encPRFOracle, hash) transcript then
        (1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
          encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) *
          (∑' target, (PMF.uniformOfFintype InputMacKey) target *
            if EncSourceGood source target then weight target else 0) else 0) ≤
    ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
      (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
        ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
          if OracleTranscriptCompatible (publicHandler id) (fixed, enc, hash) transcript then
            weight (EncPRF.transformKey enc ⟨(hash hidden).1, (hash hidden).2⟩ source) else 0 := by
  have length : (sharedLegacyTranscript transcript).length ≤ budget := by
    rw [sharedLegacyTranscript_length]
    exact lengthBound
  have bound := hiddenEncSource_weighted_mass_ge hidden source
    {rest.reference with fixedKeyOracle := Shared.expandOracle fixed}
    (sharedLegacyTranscript transcript) miss budget length fits weight
  simp_rw [sharedLegacyTranscript_compatible, Shared.restrict_expand] at bound
  exact bound

end
end Kriterion.ArgoMAC.Security
