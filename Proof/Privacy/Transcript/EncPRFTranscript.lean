import Proof.Privacy.Distribution.EncPRFDistribution
import Proof.Privacy.Transcript.RealTranscriptMass

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

/-- This function retains every external EncPRF query in either direction. -/
def encOracleTranscriptRecords : List (Sigma Garbling.oracleSpec.Answer) →
    List (PermutationRecord EncPRF.PermutationIndex Block)
  | [] => []
  | ⟨.fixedForward _ _, _⟩ :: tail => encOracleTranscriptRecords tail
  | ⟨.fixedInverse _ _, _⟩ :: tail => encOracleTranscriptRecords tail
  | ⟨.encForward index input, output⟩ :: tail =>
      ⟨.forward, .adversary, index, input, output⟩ :: encOracleTranscriptRecords tail
  | ⟨.encInverse index output, input⟩ :: tail =>
      ⟨.inverse, .adversary, index, input, output⟩ :: encOracleTranscriptRecords tail
  | ⟨.hash _, _⟩ :: tail => encOracleTranscriptRecords tail

/-- This fiber counts each queried EncPRF domain once. -/
def EncQueryDomain (history : List (PermutationRecord EncPRF.PermutationIndex Block))
    (index : EncPRF.PermutationIndex) :=
  {domain : Block // ∃ record ∈ history, record.index = index ∧ record.domain = domain}

local instance [Fintype Block]
    (history : List (PermutationRecord EncPRF.PermutationIndex Block))
    (index : EncPRF.PermutationIndex) : Fintype (EncQueryDomain history index) := by
  classical
  unfold EncQueryDomain
  infer_instance

/-- Each distinct queried domain uses at least one external record. -/
theorem encQueryDomain_sum_card_le [Fintype Block]
    (history : List (PermutationRecord EncPRF.PermutationIndex Block)) :
    (∑ index, Fintype.card (EncQueryDomain history index)) ≤ history.length := by
  classical
  let pick : (index : EncPRF.PermutationIndex) → EncQueryDomain history index →
      PermutationRecord EncPRF.PermutationIndex Block := fun _ query => Classical.choose query.2
  have picked (index) (query : EncQueryDomain history index) :
      pick index query ∈ history ∧ (pick index query).index = index ∧
        (pick index query).domain = query.1 := Classical.choose_spec query.2
  let embed : (Σ index, EncQueryDomain history index) → history.toFinset :=
    fun query => ⟨pick query.1 query.2, List.mem_toFinset.mpr (picked query.1 query.2).1⟩
  have injective : Function.Injective embed := by
    intro first second equal
    have record := congrArg Subtype.val equal
    have indices : first.1 = second.1 :=
      (picked first.1 first.2).2.1.symm.trans
        ((congrArg PermutationRecord.index record).trans (picked second.1 second.2).2.1)
    rcases first with ⟨index, first⟩
    rcases second with ⟨other, second⟩
    dsimp only at indices
    subst other
    apply congrArg (Sigma.mk index)
    apply Subtype.ext
    exact (picked index first).2.2.symm.trans
      ((congrArg PermutationRecord.domain record).trans (picked index second).2.2)
  calc
    _ = Fintype.card (Σ index, EncQueryDomain history index) := Fintype.card_sigma.symm
    _ ≤ Fintype.card history.toFinset := Fintype.card_le_of_injective embed injective
    _ = history.toFinset.card := Fintype.card_coe _
    _ ≤ history.length := List.toFinset_card_le _

/-- The EncPRF extraction uses at most one record per external query. -/
theorem encOracleTranscriptRecords_length_le
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (encOracleTranscriptRecords transcript).length ≤ transcript.length := by
  induction transcript with
  | nil => exact Nat.le_refl _
  | cons entry tail ih =>
      rcases entry with ⟨query, answer⟩
      cases query <;> simp only [encOracleTranscriptRecords, List.length_cons] <;> omega

/-- Every distinct EncPRF domain fits the external query budget. -/
theorem encExternalQueryCount_le [Fintype Block]
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑ index, Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index)) ≤
      transcript.length :=
  (encQueryDomain_sum_card_le _).trans (encOracleTranscriptRecords_length_le transcript)

/-- The shared whitening-key loss uses the external query budget. -/
theorem encQueryLoss_budget_le [Fintype Block]
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (budget : Nat)
    (lengthBound : transcript.length ≤ budget) :
    (∑ index, ((4 * Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) : Nat) : ℝ≥0∞) /
      Fintype.card Block) ≤ ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block := by
  simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, ← Finset.mul_sum]
  apply mul_le_mul_left
  exact_mod_cast Nat.mul_le_mul_left 4 ((encExternalQueryCount_le transcript).trans lengthBound)

/-- The actual handler changes only the EncPRF constraints when its EncPRF oracle changes. -/
theorem realTranscript_update_enc_iff (randomness : Garbling.Randomness)
    (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript) :
    OracleTranscriptCompatible Garbling.oracleHandler {randomness with encPRFOracle := oracle} transcript ↔
      PermutationTranscriptMatches oracle (encOracleTranscriptRecords transcript) := by
  have inverse (permutation : Equiv.Perm Block) (input output : Block) :
      permutation.symm output = input ↔ permutation input = output := by
    constructor
    · intro equal
      rw [← equal, Equiv.apply_symm_apply]
    · intro equal
      rw [← equal, Equiv.symm_apply_apply]
  induction transcript with
  | nil => simp [OracleTranscriptCompatible, PermutationTranscriptMatches, encOracleTranscriptRecords]
  | cons entry tail ih =>
      rcases entry with ⟨query, answer⟩
      cases query <;>
        simp only [OracleTranscriptCompatible, Garbling.oracleHandler, Cryptography.publicHandler, Cryptography.publicAnswer] at compatible ⊢
      all_goals have tailLaw := ih compatible.2
      all_goals simp only [Garbling.oracleHandler] at tailLaw
      all_goals rw [propext tailLaw]
      all_goals simp only [encOracleTranscriptRecords, PermutationTranscriptMatches,
        List.mem_cons, forall_eq_or_imp]
      all_goals try simp only [inverse] at compatible ⊢
      all_goals simp [compatible.1]
      all_goals first | exact fun _ => Iff.rfl | exact fun _ => inverse _ _ _

/-- A compatible reference fixes the answer at each distinct EncPRF domain. -/
theorem encTranscriptMatches_iff_domains
    (reference oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (history : List (PermutationRecord EncPRF.PermutationIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    PermutationTranscriptMatches oracle history ↔ ∀ index, ∀ query : EncQueryDomain history index,
      oracle.permutation index query.1 = reference.permutation index query.1 := by
  constructor
  · intro matching index query
    rcases query with ⟨domain, record, member, sameIndex, sameDomain⟩
    subst index
    subst domain
    exact (matching record member).trans (compatible record member).symm
  · intro matching record member
    exact (matching record.index ⟨record.domain, record, member, rfl, rfl⟩).trans
      (compatible record member)

/-- The actual EncPRF key and external transcript impose the prescribed pad equations. -/
theorem encKeyTranscript_iff (source target : InputMacKey) (difference : Block)
    (randomness : Garbling.Randomness) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (sample : (Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block)) :
    (EncPRF.transformKey ⟨sample.2⟩ (whiteningFromSplit (sample.1 ()) difference) source = target ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with encPRFOracle := ⟨sample.2⟩} transcript) ↔
      EncPadCompatible (linkingPad source target)
        (fun index (query : EncQueryDomain (encOracleTranscriptRecords transcript) index) => query.1)
        (fun index (query : EncQueryDomain (encOracleTranscriptRecords transcript) index) =>
          randomness.encPRFOracle.permutation index query.1) difference sample := by
  have reference : PermutationTranscriptMatches randomness.encPRFOracle
      (encOracleTranscriptRecords transcript) :=
    (realTranscript_update_enc_iff randomness randomness.encPRFOracle transcript compatible).mp compatible
  rw [transformKey_eq_iff_pad, realTranscript_update_enc_iff randomness _ transcript compatible,
    encTranscriptMatches_iff_domains randomness.encPRFOracle _ _ reference]
  simp only [EncPadCompatible]
  exact (forall_and).symm

/-- The finite slot count bounds the actual linked-key and actual-handler transcript event. -/
theorem encKeyTranscript_mass_ge [Fintype Block]
    (source target : InputMacKey) (difference : Block)
    (randomness : Garbling.Randomness) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (padsDistinct : ∀ index, Function.Injective (linkingPad source target index))
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    (1 - ∑ index,
      ((4 * Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) : Nat) : ℝ≥0∞) /
        Fintype.card Block) *
      (∏ index, ((Fintype.card Block : ℝ≥0∞) ^ 2)⁻¹ *
        ((Fintype.card Block - Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index)).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial) ≤
      (PMF.uniformOfFintype
        ((Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block))).toOuterMeasure
        {sample | EncPRF.transformKey ⟨sample.2⟩ (whiteningFromSplit (sample.1 ()) difference) source = target ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := ⟨sample.2⟩} transcript} := by
  have bound := encPadCompatible_mass_ge (linkingPad source target)
    (fun index (query : EncQueryDomain (encOracleTranscriptRecords transcript) index) => query.1)
    (fun index (query : EncQueryDomain (encOracleTranscriptRecords transcript) index) =>
          randomness.encPRFOracle.permutation index query.1) difference padsDistinct
    (fun _ => Subtype.val_injective)
    (fun index => (randomness.encPRFOracle.permutation index).injective.comp Subtype.val_injective) fits
  simpa only [← encKeyTranscript_iff source target difference randomness transcript compatible] using bound

/-- Independent Boolean pad pairs have the mass of one uniform target key. -/
theorem encIndependentFactor_eq [Fintype Block]
    (target : InputMacKey) (factor : EncPRF.PermutationIndex → ℝ≥0∞) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (∏ index, ((Fintype.card Block : ℝ≥0∞) ^ 2)⁻¹ * factor index) =
      (PMF.uniformOfFintype InputMacKey) target * ∏ index, factor index := by
  letI : Fintype InputMacKey := publicInputMacKeyFintype
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  rw [Finset.prod_mul_distrib, PMF.uniformOfFintype_apply]
  have count : Fintype.card InputMacKey =
      Fintype.card (EncPRF.PermutationIndex → Bool → Block) :=
    Fintype.card_congr inputKeyLabelEquiv
  rw [count, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_pow, ENNReal.inv_pow]
  simp only [Finset.prod_const, Finset.card_univ, ENNReal.inv_pow]


/-- This factor is the exact independent EncPRF transcript mass. -/
def encTranscriptFactor [Fintype Block]
    (history : List (PermutationRecord EncPRF.PermutationIndex Block)) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block - Fintype.card (EncQueryDomain history index)).factorial : ℝ≥0∞) /
    (Fintype.card Block).factorial

/-- This equivalence exposes the actual independent EncPRF permutation family. -/
def encOracleFamilyEquiv : PermutationOracle EncPRF.PermutationIndex Block ≃
    (EncPRF.PermutationIndex → Equiv.Perm Block) where
  toFun oracle := oracle.permutation
  invFun family := ⟨family⟩
  left_inv oracle := by cases oracle; rfl
  right_inv _ := rfl

/-- A compatible EncPRF reference gives the exact transcript probability. -/
theorem encTranscriptFactor_eq_mass [Fintype Block]
    (reference : PermutationOracle EncPRF.PermutationIndex Block)
    (history : List (PermutationRecord EncPRF.PermutationIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)).toOuterMeasure
      {oracle | PermutationTranscriptMatches oracle history} = encTranscriptFactor history := by
  classical
  have mapLaw := map_uniformOfFintype_equivBetween encOracleFamilyEquiv.symm
  rw [← mapLaw, PMF.toOuterMeasure_map_apply]
  have event : encOracleFamilyEquiv.symm ⁻¹' {oracle | PermutationTranscriptMatches oracle history} =
      {family | ∀ index, ∀ query : EncQueryDomain history index,
        family index query.1 = reference.permutation index query.1} := by
    ext family
    exact encTranscriptMatches_iff_domains reference _ history compatible
  rw [event]
  have familyLaw := uniformFamily_event_product (fun index =>
    {permutation : Equiv.Perm Block | ∀ query : EncQueryDomain history index,
      permutation query.1 = reference.permutation index query.1})
  apply familyLaw.trans
  apply Finset.prod_congr rfl
  intro index _
  exact indexedAssignment_mass
    (fun query : EncQueryDomain history index => query.1)
    (fun query => reference.permutation index query.1)
    Subtype.val_injective ((reference.permutation index).injective.comp Subtype.val_injective)

/-- The actual linked-key event has the uniform target-key factor and one shared query loss. -/
theorem encKeyTranscript_uniformTarget_mass_ge [Fintype Block]
    (source target : InputMacKey) (difference : Block)
    (randomness : Garbling.Randomness) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (padsDistinct : ∀ index, Function.Injective (linkingPad source target index))
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (PMF.uniformOfFintype InputMacKey) target * encTranscriptFactor (encOracleTranscriptRecords transcript) ≤
      (PMF.uniformOfFintype
        ((Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block))).toOuterMeasure
        {sample | EncPRF.transformKey ⟨sample.2⟩ (whiteningFromSplit (sample.1 ()) difference) source = target ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := ⟨sample.2⟩} transcript} := by
  letI : Fintype InputMacKey := publicInputMacKeyFintype
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  have bound := encKeyTranscript_mass_ge source target difference randomness transcript compatible padsDistinct fits
  simp_rw [mul_div_assoc] at bound
  rw [encIndependentFactor_eq target] at bound
  have loss := tsub_le_tsub_left (encQueryLoss_budget_le transcript budget lengthBound) 1
  apply le_trans _ bound
  rw [mul_assoc]
  exact mul_le_mul_left loss _

/-- This equivalence turns the shared-key count into the actual two-key oracle source. -/
def encWhiteningSourceEquiv :
    (((Unit → Block) × (EncPRF.PermutationIndex → Equiv.Perm Block)) × Block) ≃
      ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block) where
  toFun sample := ((sample.1.1 (), sample.1.1 () ^^^ sample.2), ⟨sample.1.2⟩)
  invFun sample := ((fun _ => sample.1.1, sample.2.permutation), sample.1.1 ^^^ sample.1.2)
  left_inv sample := by
    apply Prod.ext
    · apply Prod.ext
      · funext index
        cases index
        rfl
      · rfl
    · change (sample.1.1 () ^^^ (sample.1.1 () ^^^ sample.2)) = sample.2
      rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv sample := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change (sample.1.1 ^^^ (sample.1.1 ^^^ sample.1.2)) = sample.1.2
        rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · cases sample.2
      rfl

/-- A fresh uniform hash answer and the actual EncPRF oracle give the linked-key count. -/
theorem encFreshHashTranscript_mass_ge [Fintype Block]
    (source target : InputMacKey)
    (randomness : Garbling.Randomness) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (padsDistinct : ∀ index, Function.Injective (linkingPad source target index))
    (budget : Nat) (lengthBound : transcript.length ≤ budget)
    (fits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords transcript) index) ≤
      Fintype.card Block) :
    letI : Fintype InputMacKey := publicInputMacKeyFintype
    letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
    (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (PMF.uniformOfFintype InputMacKey) target * encTranscriptFactor (encOracleTranscriptRecords transcript) ≤
      (PMF.uniformOfFintype
        ((Block × Block) × PermutationOracle EncPRF.PermutationIndex Block)).toOuterMeasure
        {sample | EncPRF.transformKey sample.2 ⟨sample.1.1, sample.1.2⟩ source = target ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with encPRFOracle := sample.2} transcript} := by
  letI : Fintype InputMacKey := publicInputMacKeyFintype
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  rw [← map_uniformOfFintype_equivBetween encWhiteningSourceEquiv,
    PMF.toOuterMeasure_map_apply, uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply]
  let lower := (1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
    (PMF.uniformOfFintype InputMacKey) target * encTranscriptFactor (encOracleTranscriptRecords transcript)
  calc
    _ = ∑' difference : Block, (PMF.uniformOfFintype Block) difference * lower := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro difference
      apply mul_le_mul_right
      exact encKeyTranscript_uniformTarget_mass_ge source target difference randomness transcript
        compatible padsDistinct budget lengthBound fits

end

end Kriterion.ArgoMAC.Security
