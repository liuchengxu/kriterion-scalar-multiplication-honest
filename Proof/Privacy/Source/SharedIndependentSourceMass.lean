import Proof.Privacy.Transcript.SharedPublicTranscript
import Proof.Privacy.Source.EncSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
local instance independentSharedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance independentSharedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This source keeps the selected curve labels and samples an independent point key. -/
def sharedIndependentHiddenSourceMass [Fintype Block]
    (rest : GarblingSourceRest) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma sharedRealOracleSpec.Answer)) : ENNReal :=
  (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) ×
    ((EncPRF.PermutationIndex → Block) × InputMacKey))).toOuterMeasure
    {coin |
      let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
        (inputMacCoordinateEquiv mac, coin.2.1)
      RawGarblingMatches (sourceGatePrescription source coin.2.2 key lifts) (Shared.expandOracle coin.1) ∧
        OracleTranscriptCompatible (publicHandler id) (coin.1, rest.encPRFOracle, rest.hashOracle) transcript ∧
          EncSourceGood key coin.2.2}

private theorem uniformPair {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ENNReal) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- Compatible non-fixed answers leave the exact guarded fixed-source average. -/
theorem sharedIndependentHiddenSourceMass_fixed [Fintype Block]
    (rest : GarblingSourceRest) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (input : AffineInput) (mac : InputMac) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript) :
    sharedIndependentHiddenSourceMass rest source lifts input mac transcript =
      ∑' unused, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) unused *
        ∑' pointKey, (PMF.uniformOfFintype InputMacKey) pointKey *
          (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
            {fixed |
              let key := (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm
                (inputMacCoordinateEquiv mac, unused)
              RawGarblingMatches (sourceGatePrescription source pointKey key lifts) (Shared.expandOracle fixed) ∧
                PermutationTranscriptMatches fixed (sharedFixedTranscriptRecords transcript) ∧ EncSourceGood key pointKey} := by
  rw [sharedIndependentHiddenSourceMass, uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply, uniformPair]
  apply tsum_congr
  intro unused
  apply congrArg (_ * ·)
  apply tsum_congr
  intro pointKey
  apply congrArg (_ * ·)
  rw [PMF.toOuterMeasure_map_apply]
  apply congrArg ((PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure)
  ext fixed
  simp only [Set.mem_preimage, Set.mem_setOf_eq, sharedPublicTranscriptCompatible_iff]
  have other := (sharedNonFixedTranscriptCompatible_fixed fixed reference
    rest.encPRFOracle rest.hashOracle transcript).mpr nonfixed
  simp only [other, and_true]

end
end Kriterion.ArgoMAC.Security
