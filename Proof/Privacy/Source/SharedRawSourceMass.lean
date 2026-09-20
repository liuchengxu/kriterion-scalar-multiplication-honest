import Construction.SharedGarbling
import Proof.Privacy.Source.RealCircuitSource
import Proof.Privacy.Collision.CircuitSlotRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- This fiber puts the hash and pad uses in the same public permutation. -/
def SharedRawBucketUse {Gate : Type*} (gates : Gate → RawGatePrescription)
    (index : Shared.FixedKeyIndex) :=
  {use : Gate × Pipeline.FixedKeySlot // Shared.fixedIndex
    (fixedKeyIndex (gates use.1).location (gates use.1).window use.2) = index}

instance sharedRawBucketUseFintype {Gate : Type*} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (index : Shared.FixedKeyIndex) :
    Fintype (SharedRawBucketUse gates index) := by
  classical
  unfold SharedRawBucketUse
  infer_instance

/-- This domain uses the actual branch label and paper tweak. -/
def sharedRawBucketDomain {Gate : Type*} (gates : Gate → RawGatePrescription)
    (index : Shared.FixedKeyIndex) (use : SharedRawBucketUse gates index) : Block :=
  gateInput (gates use.1.1).location ((gates use.1.1).label use.1.2)

/-- This range uses the actual source offset and paper feed-forward. -/
def sharedRawBucketRange {Gate : Type*} (gates : Gate → RawGatePrescription)
    (index : Shared.FixedKeyIndex) (use : SharedRawBucketUse gates index) : Block :=
  (gates use.1.1).offset use.1.2 ^^^
    gateInput (gates use.1.1).location ((gates use.1.1).label use.1.2)

/-- The actual three-slot source fixes both branches in each shared bucket. -/
theorem sharedRawGarblingMatches_iff {Gate : Type} (gates : Gate → RawGatePrescription)
    (oracle : PermutationOracle Shared.FixedKeyIndex Block) :
    RawGarblingMatches gates (Shared.expandOracle oracle) ↔
      ∀ index, ∀ use : SharedRawBucketUse gates index,
        oracle.permutation index (sharedRawBucketDomain gates index use) =
          sharedRawBucketRange gates index use := by
  rw [rawGarblingMatches_iff]
  constructor
  · intro matching index use
    have assigned := matching
      (fixedKeyIndex (gates use.1.1).location (gates use.1.1).window use.1.2)
      ⟨use.1, rfl⟩
    change oracle.permutation _ _ = _ at assigned
    rw [use.2] at assigned
    exact assigned
  · intro matching index use
    have assigned := matching (Shared.fixedIndex index)
      ⟨use.1, congrArg Shared.fixedIndex use.2⟩
    exact assigned

private def sharedOracleFamilyEquiv :
    PermutationOracle Shared.FixedKeyIndex Block ≃ (Shared.FixedKeyIndex → Equiv.Perm Block) where
  toFun oracle := oracle.permutation
  invFun permutations := ⟨permutations⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Each injective shared assignment has its exact finite permutation mass. -/
theorem sharedRawGarblingMatches_mass [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription)
    (domains : ∀ index, Function.Injective (sharedRawBucketDomain gates index))
    (ranges : ∀ index, Function.Injective (sharedRawBucketRange gates index)) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle)} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - Fintype.card (SharedRawBucketUse gates index)).factorial : ENNReal) /
          (Fintype.card Block).factorial := by
  have family := uniformFamily_event_product (fun index =>
    {permutation : Equiv.Perm Block | ∀ use : SharedRawBucketUse gates index,
      permutation (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use})
  have oracleLaw := map_uniformOfFintype_equivBetween sharedOracleFamilyEquiv
  rw [← oracleLaw, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at family
  have same : {oracle : PermutationOracle Shared.FixedKeyIndex Block |
      ∀ index, oracle.permutation index ∈ {permutation : Equiv.Perm Block |
        ∀ use : SharedRawBucketUse gates index,
          permutation (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use}} =
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle)} := by
    ext oracle
    exact (sharedRawGarblingMatches_iff gates oracle).symm
  change (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure _ = _ at family
  dsimp only [sharedOracleFamilyEquiv, Equiv.coe_fn_mk] at family
  rw [same] at family
  rw [family]
  apply Finset.prod_congr rfl
  intro index _
  exact indexedAssignment_mass _ _ (domains index) (ranges index)

/-- The exact shared mass applies to the actual full-hash and ciphertext source fiber. -/
theorem sharedActualFullCircuitSource_mass [Fintype Block]
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (domains : ∀ index, Function.Injective (sharedRawBucketDomain
      (sourceGatePrescription source (EncPRF.transformKey encOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey) inputKey lifts) index))
    (ranges : ∀ index, Function.Injective (sharedRawBucketRange
      (sourceGatePrescription source (EncPRF.transformKey encOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey) inputKey lifts) index)) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
        (Shared.expandOracle oracle) encOracle hashOracle inputKey = (lifts, sourceCiphertexts source)} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - Fintype.card (SharedRawBucketUse
          (sourceGatePrescription source (EncPRF.transformKey encOracle
            (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey) inputKey lifts) index)).factorial : ENNReal) /
          (Fintype.card Block).factorial := by
  have events : {oracle : PermutationOracle Shared.FixedKeyIndex Block |
      actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
        (Shared.expandOracle oracle) encOracle hashOracle inputKey = (lifts, sourceCiphertexts source)} =
      {oracle | RawGarblingMatches (sourceGatePrescription source (EncPRF.transformKey encOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey) inputKey lifts) (Shared.expandOracle oracle)} := by
    ext oracle
    exact actualFullCircuitSource_fiber outputKeys pointRandomness bridgeKey r1 r2 mask
      (Shared.expandOracle oracle) encOracle hashOracle inputKey source lifts randomizers residues
  rw [events]
  exact sharedRawGarblingMatches_mass _ domains ranges

end
end Kriterion.ArgoMAC.Security
