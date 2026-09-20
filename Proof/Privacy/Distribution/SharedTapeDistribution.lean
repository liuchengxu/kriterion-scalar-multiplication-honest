import Proof.Privacy.Distribution.TapeDistribution
import Proof.SharedOracle
import Solution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype

/-- The retained tape contains the actual shared fixed oracle. -/
abbrev SharedOffsetRest := {rest : GarblingOffsetRest //
  Shared.expandOracle (Shared.restrictOracle rest.2.2.fixedKeyOracle) = rest.2.2.fixedKeyOracle}

/-- The shared tape separates point offsets from the retained shared oracle data. -/
def sharedRandomnessPointEquiv [FieldCertificate] [GroupCertificate]
    (construction : Construction) : Shared.Randomness ≃ NonzeroPointOffsets construction × SharedOffsetRest where
  toFun randomness := ((garblingRandomnessPointEquiv construction randomness.val).1,
    ⟨(garblingRandomnessPointEquiv construction randomness.val).2, randomness.property⟩)
  invFun sample := ⟨(garblingRandomnessPointEquiv construction).symm (sample.1, sample.2.val), sample.2.property⟩
  left_inv randomness := by
    apply Subtype.ext
    exact (garblingRandomnessPointEquiv construction).symm_apply_apply randomness.val
  right_inv sample := by
    have restored := (garblingRandomnessPointEquiv construction).apply_symm_apply (sample.1, sample.2.val)
    apply Prod.ext
    · exact congrArg (fun pair : NonzeroPointOffsets construction × GarblingOffsetRest => pair.1) restored
    · apply Subtype.ext
      exact congrArg (fun pair : NonzeroPointOffsets construction × GarblingOffsetRest => pair.2) restored

instance sharedOffsetRestNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedOffsetRest :=
  ⟨(sharedRandomnessPointEquiv construction (Shared.Randomness.ofLegacy (Seed.randomness 0))).2⟩

/-- The shared point split has the exact uniform source law. -/
theorem sharedRandomTape_pointSplit [FieldCertificate] [GroupCertificate]
    (construction : Construction) (witness : Shared.Randomness) (parameter : Nat) :
    (uniformRandomTape Shared.Randomness witness parameter).map (sharedRandomnessPointEquiv construction) =
      PMF.uniformOfFintype (NonzeroPointOffsets construction × SharedOffsetRest) := by
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  rw [uniformRandomTape, uniformTape_eq]
  exact uniform_map_equiv (sharedRandomnessPointEquiv construction)

/-- The embedding removes only the restriction against identity offsets. -/
def sharedPointTapeEmbed [FieldCertificate] [GroupCertificate] (construction : Construction)
    (sample : NonzeroPointOffsets construction × SharedOffsetRest) : OffsetRandomness × SharedOffsetRest :=
  (sample.1.val, sample.2)

/-- The embedding preserves every source point and every retained shared tape value. -/
theorem sharedPointTapeEmbed_injective [FieldCertificate] [GroupCertificate] (construction : Construction) :
    Function.Injective (sharedPointTapeEmbed construction) := by
  intro first second same
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun pair : OffsetRandomness × SharedOffsetRest => pair.1) same
  · exact congrArg (fun pair : OffsetRandomness × SharedOffsetRest => pair.2) same

/-- The shared tape pays only the nonidentity-offset restriction for every observation. -/
theorem sharedRandomTape_point_observation_bound [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (construction : Construction)
    (witness : Shared.Randomness) (parameter : Nat)
    (observe : OffsetRandomness × SharedOffsetRest → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype (OffsetRandomness × SharedOffsetRest)).bind observe).toOuterMeasure event).toReal -
      (((uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
        observe (sharedPointTapeEmbed construction
          (sharedRandomnessPointEquiv construction randomness)))).toOuterMeasure event).toReal| ≤
      (2 : ℝ) ^ (-240 : ℤ) := by
  have bound := uniformEmbedding_observation_bound (sharedPointTapeEmbed construction)
    (sharedPointTapeEmbed_injective construction) observe event
  have actual : (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      observe (sharedPointTapeEmbed construction (sharedRandomnessPointEquiv construction randomness))) =
      (PMF.uniformOfFintype (NonzeroPointOffsets construction × SharedOffsetRest)).bind
        (observe ∘ sharedPointTapeEmbed construction) := by
    rw [← sharedRandomTape_pointSplit construction witness parameter, PMF.bind_map]
    rfl
  rw [actual]
  apply bound.trans
  rw [Fintype.card_prod (α := NonzeroPointOffsets construction) (β := SharedOffsetRest),
    Fintype.card_prod (α := OffsetRandomness) (β := SharedOffsetRest), Nat.cast_mul, Nat.cast_mul]
  rw [mul_div_mul_right _ _ (show (Fintype.card SharedOffsetRest : ℝ) ≠ 0 from
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact nonzeroPointOffsets_card_loss construction

end
end Kriterion.ArgoMAC.Security
