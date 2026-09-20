import Proof.Privacy.Source.SharedCurveKeyEquiv

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
open scoped ENNReal
noncomputable section
local instance curveIndependentMassFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveIndependentMassNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem uniformPair {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ENNReal) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- The pad change of variables preserves every weighted independent-key source. -/
theorem curveHiddenKeys_weighted_eq [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool)
    (weight : (EncPRF.PermutationIndex → Block) × InputMacKey → ENNReal) :
    (∑' pads, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) pads *
      ∑' key, (PMF.uniformOfFintype InputMacKey) key * weight (curveHiddenKeysEquiv selected (pads, key))) =
      ∑' unused, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) unused *
        ∑' pointKey, (PMF.uniformOfFintype InputMacKey) pointKey * weight (unused, pointKey) := by
  rw [← uniformPair (fun pair => weight (curveHiddenKeysEquiv selected pair)), ← uniformPair weight]
  simpa only [PMF.uniformOfFintype_apply] using (curveHiddenKeysEquiv selected).tsum_eq
    (fun sample => (PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × InputMacKey)) sample * weight sample)

/-- The pad average is exactly the guarded independent point-key source mass. -/
theorem curveHidden_independent_average_eq [Fintype Block]
    (context : Context) (hidden : HiddenPublicSample)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    (∑' pads, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) pads *
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixed | RawGarblingMatches ((({context with hiddenPointPads := pads}).curveHidden key).gates
              (hidden, curveUnused key)) (Shared.expandOracle fixed) ∧
            PermutationTranscriptMatches fixed history ∧
              ¬ curveHiddenPadBad {context with hiddenPointPads := pads} key}) =
    ∑' unused, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) unused *
      ∑' pointKey, (PMF.uniformOfFintype InputMacKey) pointKey *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixed | RawGarblingMatches (sourceGatePrescription (context.source hidden)
              pointKey (context.curveKey unused) (context.lifts hidden)) (Shared.expandOracle fixed) ∧
            PermutationTranscriptMatches fixed history ∧ EncSourceGood (context.curveKey unused) pointKey} := by
  rw [← curveHiddenKeys_weighted_eq (inputSelectedLabelBit context.input)
    (fun sample => (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {fixed | RawGarblingMatches (sourceGatePrescription (context.source hidden)
          sample.2 (context.curveKey sample.1) (context.lifts hidden)) (Shared.expandOracle fixed) ∧
        PermutationTranscriptMatches fixed history ∧ EncSourceGood (context.curveKey sample.1) sample.2})]
  apply tsum_congr
  intro pads
  apply congrArg (_ * ·)
  apply tsum_congr
  intro key
  apply congrArg (_ * ·)
  rw [curveHiddenKeys_source context pads key]
  apply congrArg ((PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure)
  ext fixed
  rw [independent_gates]
  have sourceEq : ({context with hiddenPointPads := pads}).source hidden = context.source hidden := by
    unfold Context.source
    rfl
  have liftsEq : ({context with hiddenPointPads := pads}).lifts hidden = context.lifts hidden := by
    unfold Context.lifts
    rw [sourceEq]
  simp only [Set.mem_setOf_eq, curveHidden_source_eq, curveHidden_lifts_eq, sourceEq, liftsEq]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (curveHidden_pad_good_iff {context with hiddenPointPads := pads} key).symm)

end
end Kriterion.ArgoMAC.Security.SharedRetained
