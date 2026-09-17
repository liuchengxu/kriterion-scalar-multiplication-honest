/-
This file compares the gate formula with `Latex/prf_choice.tex`.
The source commit is `e2dcf4d540b2708e13cd21090df759051119a116`.
The comparison keeps the digit tweak explicit.
The uniform law below applies to one fixed tweak.
It does not identify a shared bucket across different tweaks.
-/

import Construction.ArgoMAC.Pipeline
import Proof.Privacy.Simulator.Simulator

namespace Kriterion.ArgoMAC.PaperConstruction

open BN254 Cryptography Pipeline

/-- The paper feeds the tweaked label forward. -/
def paperBlock (permutation : Equiv.Perm Block) (tweak label : Block) : Block :=
  permutation (label ^^^ tweak) ^^^ (label ^^^ tweak)

/-- The entry feeds the original label forward. -/
def entryBlock (permutation : Equiv.Perm Block) (tweak label : Block) : Block :=
  daviesMeyer ((tweakEquiv tweak).trans permutation) label

/-- The two block formulas differ by exactly the public tweak. -/
theorem entryBlock_eq (permutation : Equiv.Perm Block) (tweak label : Block) :
    entryBlock permutation tweak label = paperBlock permutation tweak label ^^^ tweak := by
  simp only [entryBlock, paperBlock, daviesMeyer, Cryptography.xor, Equiv.trans_apply,
    tweakEquiv, Equiv.coe_fn_mk]
  rw [BitVec.xor_assoc, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- This map translates each permutation output by one fixed tweak. -/
def outputTranslation (tweak : Block) : Equiv.Perm (Equiv.Perm Block) where
  toFun permutation := permutation.trans (tweakEquiv tweak)
  invFun permutation := permutation.trans (tweakEquiv tweak)
  left_inv permutation := by
    apply Equiv.ext
    intro block
    simp [Equiv.trans_apply, tweakEquiv, BitVec.xor_assoc]
  right_inv permutation := by
    apply Equiv.ext
    intro block
    simp [Equiv.trans_apply, tweakEquiv, BitVec.xor_assoc]

/-- One fixed output translation makes the block formulas equal. -/
theorem entryBlock_eq_translatedPaper (permutation : Equiv.Perm Block)
    (tweak label : Block) :
    entryBlock permutation tweak label =
      paperBlock (outputTranslation tweak permutation) tweak label := by
  rw [entryBlock_eq]
  simp only [paperBlock, outputTranslation, Equiv.coe_fn_mk, Equiv.trans_apply,
    tweakEquiv]
  rw [BitVec.xor_assoc (permutation (label ^^^ tweak)) tweak]
  rw [BitVec.xor_comm tweak (label ^^^ tweak)]
  exact BitVec.xor_assoc _ _ _

/-- The inverse query must translate its input by the same tweak. -/
theorem outputTranslation_inverse (permutation : Equiv.Perm Block)
    (tweak output : Block) :
    (outputTranslation tweak permutation).symm output =
      permutation.symm (output ^^^ tweak) := rfl

/-- One fixed output translation preserves a uniform permutation. -/
theorem outputTranslation_uniform (tweak : Block) :
    (PMF.uniformOfFintype (Equiv.Perm Block)).map (outputTranslation tweak) =
      PMF.uniformOfFintype (Equiv.Perm Block) :=
  Security.map_uniformOfFintype_equiv (outputTranslation tweak)

/-- The paper joins three blocks before it reduces the result modulo the field prime. -/
def paperHashBytes (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) : BitVec 384 :=
  paperBlock (permutations.hash 2) tweak label ++
    paperBlock (permutations.hash 1) tweak label ++
      paperBlock (permutations.hash 0) tweak label

/-- This reference applies the paper block formula to the two entry pad slots. -/
def paperPadBytes (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) : BitVec 256 :=
  paperBlock (permutations.pad 1) tweak label ++
    paperBlock (permutations.pad 0) tweak label

/-- This map gives all five slots the same input tweak. -/
def inputTranslation (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak : Block) : BitAdaptor.FixedKeyPermutations where
  hash slot := (tweakEquiv tweak).trans (permutations.hash slot)
  pad slot := (tweakEquiv tweak).trans (permutations.pad slot)

/-- The byte relation holds before field reduction. -/
theorem hashBytes_eq (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) :
    BitAdaptor.hashBytes (inputTranslation permutations tweak) label =
      paperHashBytes permutations tweak label ^^^ (tweak ++ tweak ++ tweak) := by
  change (entryBlock (permutations.hash 2) tweak label ++
    entryBlock (permutations.hash 1) tweak label ++
    entryBlock (permutations.hash 0) tweak label) =
      paperHashBytes permutations tweak label ^^^ (tweak ++ tweak ++ tweak)
  simp only [entryBlock_eq, paperHashBytes]
  rw [← BitVec.xor_append, ← BitVec.xor_append]

/-- The pad relation uses a 256-bit copy of the public tweak. -/
theorem padBytes_eq (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) :
    BitAdaptor.padBytes (inputTranslation permutations tweak) label =
      paperPadBytes permutations tweak label ^^^ (tweak ++ tweak) := by
  change (entryBlock (permutations.pad 1) tweak label ++
    entryBlock (permutations.pad 0) tweak label) =
      paperPadBytes permutations tweak label ^^^ (tweak ++ tweak)
  simp only [entryBlock_eq, paperPadBytes]
  exact BitVec.xor_append.symm

/-- The field relation retains the XOR inside the reduction. -/
theorem hashToField_eq (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) :
    (BitAdaptor.fixedKeyOracle (inputTranslation permutations tweak)).hashToField label =
      ((paperHashBytes permutations tweak label ^^^
        (tweak ++ tweak ++ tweak)).toNat : BaseField) := by
  exact congrArg (fun bytes : BitVec 384 => (bytes.toNat : BaseField))
    (hashBytes_eq permutations tweak label)

/-- The ciphertext relation retains the field encoding and translates only the pad. -/
theorem encrypt_eq (permutations : BitAdaptor.FixedKeyPermutations)
    (tweak label : Block) (message : BaseField) :
    (BitAdaptor.fixedKeyOracle (inputTranslation permutations tweak)).encrypt label message =
      (paperPadBytes permutations tweak label ^^^ (tweak ++ tweak)) ^^^
        BitAdaptor.fieldBytes message := by
  exact congrArg (fun pad => pad ^^^ BitAdaptor.fieldBytes message)
    (padBytes_eq permutations tweak label)

/-- This family reads the exact bucket slots from the entry oracle. -/
def bucketPermutations (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) : BitAdaptor.FixedKeyPermutations where
  hash slot := oracle.permutation {
    kind := location.kind
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .hash slot }
  pad slot := oracle.permutation {
    kind := location.kind
    position := ⟨position % coordinateBitCount, Nat.mod_lt _ (by decide)⟩
    slot := .pad slot }

/-- The formula comparison applies to the actual entry gate. -/
theorem fixedKeyPermutations_eq (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) :
    fixedKeyPermutations oracle location position =
      inputTranslation (bucketPermutations oracle location position) location.tweak := rfl

/-- The actual gate applies the field reduction after the byte translation. -/
theorem fixedKeyGate_hashToField_eq (oracle : PermutationOracle FixedKeyIndex Block)
    (location : FixedKeyLocation) (position : Nat) (label : Block) :
    (fixedKeyGate oracle location position).hashToField label =
      ((paperHashBytes (bucketPermutations oracle location position) location.tweak label ^^^
        (location.tweak ++ location.tweak ++ location.tweak)).toNat : BaseField) := by
  unfold fixedKeyGate
  rw [fixedKeyPermutations_eq]
  exact hashToField_eq _ _ _

/-- One permutation cannot translate both formulas for two different tweaks. -/
theorem sharedTranslation_requires_equal_tweaks (entry paper : Equiv.Perm Block)
    (first second : Block)
    (firstEqual : ∀ label, entryBlock entry first label = paperBlock paper first label)
    (secondEqual : ∀ label, entryBlock entry second label = paperBlock paper second label) :
    first = second := by
  have one := firstEqual first
  have two := secondEqual second
  simp only [entryBlock, paperBlock, daviesMeyer, Cryptography.xor, Equiv.trans_apply,
    tweakEquiv, Equiv.coe_fn_mk, BitVec.xor_self, BitVec.xor_zero] at one two
  have same : entry 0 ^^^ first = entry 0 ^^^ second := one.trans two.symm
  have cancel := congrArg (fun block => entry 0 ^^^ block) same
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using cancel

/-- The proved entry uses five slots and 91 digit positions. -/
theorem variant_parameters : bucketSlotCount = 5 ∧ digitsPerBucket = 91 ∧
    pointBucketCount = 15240 ∧ curveBucketCount = 6350 := by decide

end Kriterion.ArgoMAC.PaperConstruction
