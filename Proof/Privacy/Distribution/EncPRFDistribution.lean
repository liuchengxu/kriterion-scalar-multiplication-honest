import Proof.Privacy.Collision.SlotRatio
import Proof.Privacy.Programming.Linking

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

/-- This equivalence separates the first whitening key from the key difference. -/
def whiteningSplitEquiv : (Block × Block) ≃ (Block × Block) where
  toFun keys := (keys.1, keys.1 ^^^ keys.2)
  invFun split := (split.1, split.1 ^^^ split.2)
  left_inv keys := by
    dsimp only
    rw [show keys.1 ^^^ (keys.1 ^^^ keys.2) = keys.2 from xorSelfCancel _ _]
  right_inv split := by
    dsimp only
    rw [show split.1 ^^^ (split.1 ^^^ split.2) = split.2 from xorSelfCancel _ _]

/-- Both whitening coordinates remain independent and uniform. -/
theorem map_uniform_whiteningSplit :
    (PMF.uniformOfFintype (Block × Block)).map whiteningSplitEquiv =
      PMF.uniformOfFintype (Block × Block) :=
  map_uniformOfFintype_equivBetween whiteningSplitEquiv

/-- This pair reconstructs the whitening keys from the first key and their difference. -/
def whiteningFromSplit (first difference : Block) : WhiteningKeys :=
  ⟨first, first ^^^ difference⟩

/-- The actual Even--Mansour equation has the shared-slot form. -/
theorem evenMansour_eq_iff_slot (permutation : Equiv.Perm Block)
    (first difference output : Block) (bit : Bool) :
    evenMansour permutation (whiteningFromSplit first difference) bit = output ↔
      permutation (first ^^^ encodeBit bit) = (output ^^^ difference) ^^^ first := by
  simp only [evenMansour, whiteningFromSplit, Cryptography.xor]
  constructor
  · intro equal
    have shifted := congrArg (fun value => value ^^^ (first ^^^ difference)) equal
    have result : permutation (first ^^^ encodeBit bit) = output ^^^ (first ^^^ difference) := by
      simpa only [BitVec.xor_comm (encodeBit bit) first, BitVec.xor_assoc,
        BitVec.xor_self, BitVec.xor_zero] using shifted
    exact result.trans (by ac_rfl)
  · intro equal
    rw [BitVec.xor_comm (encodeBit bit) first, equal]
    simp only [BitVec.xor_assoc, show first ^^^ (first ^^^ difference) = difference from
      xorSelfCancel _ _, BitVec.xor_self, BitVec.xor_zero]

/-- The two counter encodings are distinct. -/
theorem encodeBit_injective : Function.Injective encodeBit := by
  intro first second equal
  cases first <;> cases second <;> simp_all [encodeBit]

/-- This function reads one label from the actual input-key representation. -/
def inputKeyLabel (key : InputMacKey) (index : EncPRF.PermutationIndex) (bit : Bool) : Block :=
  BitAdaptor.encode ((match index.1 with
    | .x => key.x
    | .y => key.y).get index.2) bit

/-- The input key contains one independent label for each coordinate, bit, and branch. -/
def inputKeyLabelEquiv : InputMacKey ≃ (EncPRF.PermutationIndex → Bool → Block) where
  toFun := inputKeyLabel
  invFun labels := {
    x := Vector.ofFn fun index => ⟨labels (.x, index) false, labels (.x, index) true⟩
    y := Vector.ofFn fun index => ⟨labels (.y, index) false, labels (.y, index) true⟩ }
  left_inv key := by
    have xEqual : (Vector.ofFn fun index =>
        ⟨inputKeyLabel key (.x, index) false, inputKeyLabel key (.x, index) true⟩ :
          CoordinateMacKey) = key.x := by
      apply Vector.ext
      intro index valid
      simp only [inputKeyLabel, BitAdaptor.encode, Vector.getElem_ofFn, Bool.false_eq_true,
        ↓reduceIte]
      rfl
    have yEqual : (Vector.ofFn fun index =>
        ⟨inputKeyLabel key (.y, index) false, inputKeyLabel key (.y, index) true⟩ :
          CoordinateMacKey) = key.y := by
      apply Vector.ext
      intro index valid
      simp only [inputKeyLabel, BitAdaptor.encode, Vector.getElem_ofFn, Bool.false_eq_true,
        ↓reduceIte]
      rfl
    dsimp only
    rw [xEqual, yEqual]
  right_inv labels := by
    funext index bit
    rcases index with ⟨coordinate, index⟩
    cases coordinate <;> cases bit <;> simp [inputKeyLabel, BitAdaptor.encode]

/-- The actual label transform uses the pad from its permutation bucket. -/
theorem inputKeyLabel_transform (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (source : InputMacKey)
    (index : EncPRF.PermutationIndex) (bit : Bool) :
    inputKeyLabel (EncPRF.transformKey oracle keys source) index bit =
      encrypt (evenMansour (oracle.permutation index) keys bit) (inputKeyLabel source index bit) := by
  rcases index with ⟨coordinate, index⟩
  cases coordinate <;> cases bit <;>
    simp [inputKeyLabel, EncPRF.transformKey, EncPRF.transformCoordinateKey,
      BitAdaptor.encode, EncPRF.transformAt, EncPRF.evenMansourPad] <;> rfl

/-- The source and target labels determine the required EncPRF pad. -/
def linkingPad (source target : InputMacKey) (index : EncPRF.PermutationIndex)
    (bit : Bool) : Block := inputKeyLabel target index bit ^^^ inputKeyLabel source index bit

/-- A fixed source key permutes the uniform target labels into uniform pads. -/
def linkingPadEquiv (source : InputMacKey) :
    InputMacKey ≃ (EncPRF.PermutationIndex → Bool → Block) :=
  inputKeyLabelEquiv.trans (Equiv.piCongrRight fun index =>
    Equiv.piCongrRight fun bit =>
      (show Function.Involutive (fun label : Block => label ^^^ inputKeyLabel source index bit) from
        fun label => by simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]).toPerm)

/-- The pad equivalence gives the actual source-target pad equation. -/
theorem linkingPadEquiv_apply (source target : InputMacKey) :
    linkingPadEquiv source target = linkingPad source target := rfl

/-- Uniform target keys give uniform pads, including both branches of every bucket. -/
theorem map_uniform_linkingPad [Fintype Block] (source : InputMacKey) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (PMF.uniformOfFintype InputMacKey).map (linkingPad source) =
      PMF.uniformOfFintype (EncPRF.PermutationIndex → Bool → Block) := by
  letI : Fintype InputMacKey := publicInputMacKeyFintype
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  exact map_uniformOfFintype_equivBetween (linkingPadEquiv source)

/-- The actual key transform is equivalent to all prescribed pad equations. -/
theorem transformKey_eq_iff_pad (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (keys : WhiteningKeys) (source target : InputMacKey) :
    EncPRF.transformKey oracle keys source = target ↔
      ∀ index bit, evenMansour (oracle.permutation index) keys bit = linkingPad source target index bit := by
  rw [← inputKeyLabelEquiv.injective.eq_iff]
  simp only [funext_iff, inputKeyLabelEquiv, Equiv.coe_fn_mk, inputKeyLabel_transform,
    linkingPad, encrypt, Cryptography.xor]
  apply forall_congr'
  intro index
  apply forall_congr'
  intro bit
  constructor
  · intro equal
    have shifted := congrArg (fun value => value ^^^ inputKeyLabel source index bit) equal
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using shifted
  · intro equal
    rw [equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- This event fixes the actual EncPRF pads and every public query pair. -/
def EncPadCompatible {Queries : EncPRF.PermutationIndex → Type*}
    (pad : EncPRF.PermutationIndex → Bool → Block)
    (domain range : ∀ index, Queries index → Block) (difference : Block)
    (sample : (Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block)) : Prop :=
  ∀ index,
    (∀ bit, evenMansour (sample.2 index)
      (whiteningFromSplit (sample.1 ()) difference) bit = pad index bit) ∧
    ∀ query, sample.2 index (domain index query) = range index query

set_option maxRecDepth 2048 in
/-- The finite slot count applies to all actual EncPRF permutation buckets. -/
theorem encPadCompatible_mass_ge [Fintype Block] {Queries : EncPRF.PermutationIndex → Type*}
    [∀ index, Fintype (Queries index)]
    (pad : EncPRF.PermutationIndex → Bool → Block)
    (domain range : ∀ index, Queries index → Block) (difference : Block)
    (padsDistinct : ∀ index, Function.Injective (pad index))
    (domainsDistinct : ∀ index, Function.Injective (domain index))
    (rangesDistinct : ∀ index, Function.Injective (range index))
    (fits : ∀ index, 2 + Fintype.card (Queries index) ≤ Fintype.card Block) :
    (1 - ∑ index,
      ((4 * Fintype.card (Queries index) : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∏ index, ((Fintype.card Block : ℝ≥0∞) ^ 2)⁻¹ *
        ((Fintype.card Block - Fintype.card (Queries index)).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial) ≤
      (PMF.uniformOfFintype
        ((Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block))).toOuterMeasure
          {sample | EncPadCompatible pad domain range difference sample} := by
  have bound := sharedSlots_mass_ge (fun _ : EncPRF.PermutationIndex => ())
    (fun _ => 0) (fun _ => encodeBit)
    (fun index bit => pad index bit ^^^ difference) domain range
    (fun _ => encodeBit_injective)
    (fun index => slotOutput_injective (pad index) (padsDistinct index) difference)
    domainsDistinct rangesDistinct (by simpa using fits)
  have zeroShift (value : Block) : value ^^^ (0 : Block) = value := BitVec.xor_zero
  dsimp only [sharedSlotsCompatible] at bound
  simp only [zeroShift] at bound
  simpa only [Fintype.card_bool, Nat.reduceMul, EncPadCompatible,
    BitVec.xor_zero, evenMansour_eq_iff_slot] using bound

/-- Distinct Boolean pad values give the required injective assignment. -/
theorem booleanPad_injective_iff (pad : Bool → Block) :
    Function.Injective pad ↔ pad false ≠ pad true := by
  constructor
  · intro injective equal
    exact Bool.false_ne_true (injective equal)
  · intro distinct first second equal
    cases first <;> cases second <;> simp_all

/-- Equal Boolean pads have one free block. -/
def equalBooleanPadsEquiv : {pad : Bool → Block // pad false = pad true} ≃ Block where
  toFun pad := pad.1 false
  invFun block := ⟨fun _ => block, rfl⟩
  left_inv pad := by
    apply Subtype.ext
    funext bit
    cases bit
    · rfl
    · exact pad.2
  right_inv block := rfl

/-- One uniform Boolean pad pair collides with inverse block mass. -/
theorem uniformBooleanPads_collision_mass [Fintype Block] :
    (PMF.uniformOfFintype (Bool → Block)).toOuterMeasure
      {pad | pad false = pad true} = (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have count : Fintype.card ({pad : Bool → Block | pad false = pad true} : Set _) =
      Fintype.card Block := Fintype.card_congr equalBooleanPadsEquiv
  rw [count, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  simpa only [pow_two, mul_one, one_div] using
    (ENNReal.mul_div_mul_left (c := (Fintype.card Block : ℝ≥0∞))
      1 (Fintype.card Block) (by exact_mod_cast Fintype.card_ne_zero) (by simp))

/-- A uniform pad tape has at most one inverse block loss per EncPRF bucket. -/
theorem uniformEncPads_collision_mass_le [Fintype Block] :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Bool → Block)).toOuterMeasure
      {pads | ∃ index, pads index false = pads index true} ≤
        (508 : ℝ≥0∞) / Fintype.card Block := by
  classical
  have marginal (index : EncPRF.PermutationIndex) :
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Bool → Block)).map
        (fun pads => pads index) = PMF.uniformOfFintype (Bool → Block) := by
    have law := congrArg (fun distribution => distribution.map Prod.fst)
      (map_uniformOfFintype_equivBetween (Equiv.piSplitAt index (fun _ => Bool → Block)))
    simpa only [Function.comp_def, Equiv.piSplitAt_apply, PMF.map_comp, map_uniform_prod_fst] using law
  rw [show {pads : EncPRF.PermutationIndex → Bool → Block |
      ∃ index, pads index false = pads index true} =
      ⋃ index, {pads | pads index false = pads index true} by ext pads; simp]
  apply (MeasureTheory.measure_iUnion_le _).trans
  have each (index : EncPRF.PermutationIndex) :
      (PMF.uniformOfFintype (EncPRF.PermutationIndex → Bool → Block)).toOuterMeasure
        {pads | pads index false = pads index true} =
      (Fintype.card Block : ℝ≥0∞)⁻¹ := by
    have law := uniformBooleanPads_collision_mass
    rw [← marginal index, PMF.toOuterMeasure_map_apply] at law
    exact law
  simp_rw [each]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have count : Fintype.card EncPRF.PermutationIndex = 508 := by
    have coordinate : Fintype.card EncPRF.Coordinate = 2 := by decide
    simp [EncPRF.PermutationIndex, coordinateBitCount, coordinate]
  rw [count]
  simp only [div_eq_mul_inv]
  rfl

/-- Uniform target keys meet the actual pad-distinctness condition except for 508/N mass. -/
theorem linkingPad_collision_mass_le [Fintype Block] (source : InputMacKey) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {target | ∃ index, linkingPad source target index false = linkingPad source target index true} ≤
        (508 : ℝ≥0∞) / Fintype.card Block := by
  letI : Fintype InputMacKey := publicInputMacKeyFintype
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  have bound := uniformEncPads_collision_mass_le
  rw [← map_uniform_linkingPad source, PMF.toOuterMeasure_map_apply] at bound
  exact bound

end

end Kriterion.ArgoMAC.Security
