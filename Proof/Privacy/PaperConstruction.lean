/-
This file checks the block formula against `Latex/prf_choice.tex`.
The paper commit is `e2dcf4d540b2708e13cd21090df759051119a116`.
The equality holds for every label and every tweak in a shared bucket.
-/

import Construction.ArgoMAC.Pipeline

namespace Kriterion.ArgoMAC.PaperConstruction
open BN254 Cryptography Pipeline

/-- The paper feeds the tweaked label forward. -/
def paperBlock (permutation : Equiv.Perm Block) (tweak label : Block) : Block :=
  permutation (label ^^^ tweak) ^^^ (label ^^^ tweak)

/-- The implementation applies Davies--Meyer to the tweaked label. -/
def entryBlock (permutation : Equiv.Perm Block) (tweak label : Block) : Block :=
  daviesMeyer permutation (label ^^^ tweak)

/-- The implementation uses the exact paper formula for every tweak. -/
theorem entryBlock_eq (permutation : Equiv.Perm Block) (tweak label : Block) :
    entryBlock permutation tweak label = paperBlock permutation tweak label := rfl

/-- The paper joins three blocks before field reduction. -/
def paperHashBytes (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) : BitVec 384 :=
  paperBlock (permutations.hash 2) tweak label ++
    paperBlock (permutations.hash 1) tweak label ++
      paperBlock (permutations.hash 0) tweak label

/-- The pad uses the same block formula in its two slots. -/
def paperPadBytes (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) : BitVec 256 :=
  paperBlock (permutations.pad 1) tweak label ++
    paperBlock (permutations.pad 0) tweak label

/-- The actual gate agrees with the paper before and after field reduction. -/
theorem fixedKeyGate_hashToField_eq (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) (label : Block) :
    (fixedKeyGate oracle location position).hashToField label =
      ((paperHashBytes (fixedKeyPermutations oracle location position) location.tweak label).toNat :
        BaseField) := rfl

/-- The actual ciphertext uses the paper feed-forward term. -/
theorem fixedKeyGate_encrypt_eq (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) (label : Block) (message : BaseField) :
    (fixedKeyGate oracle location position).encrypt label message =
      paperPadBytes (fixedKeyPermutations oracle location position) location.tweak label ^^^
        BitAdaptor.fieldBytes message := rfl

/-- The original-label formula differs whenever the public tweak is nonzero. -/
theorem originalLabel_ne_paper (permutation : Equiv.Perm Block) (tweak label : Block)
    (nonzero : tweak ≠ (0#128)) :
    permutation (label ^^^ tweak) ^^^ label ≠ paperBlock permutation tweak label := by
  intro same
  have shifted := congrArg (fun value => permutation (label ^^^ tweak) ^^^ value) same
  have labels : label = label ^^^ tweak := by
    simpa only [paperBlock, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using shifted
  have cancel := congrArg (fun value => label ^^^ value) labels
  apply nonzero
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using cancel.symm

/-- The paper assigns a distinct tweak to each digit and the curve sentinel. -/
theorem paper_tweaks (row : Fin FieldMacToECMac.outputMacCount)
    (coordinate : PointCoordinate) (adaptor : PointAdaptor) (curve : CurveAdaptor) :
    (FixedKeyLocation.point row coordinate adaptor).tweak = BitVec.ofNat 128 row.val ∧
      (FixedKeyLocation.curve curve).tweak = BitVec.ofNat 128 91 := ⟨rfl, rfl⟩

/-- This parameter check records the tree's counts for the three shared
families: five bucket slots, one output digit per bucket, and the point and
curve bucket counts that follow from the 12 point digit adaptors per
coordinate. -/
theorem variant_parameters : bucketSlotCount = 5 ∧ digitsPerBucket = 91 ∧
    pointBucketCount = 15240 ∧ curveBucketCount = 6350 := by decide

end Kriterion.ArgoMAC.PaperConstruction
