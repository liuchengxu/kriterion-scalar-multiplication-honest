import Proof.Privacy.Source.FullSourceGood
import Proof.Privacy.Source.Invalid.InvalidSourceTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- The complete full source has exactly the field and quotient coordinates. -/
def completeCircuitSourceEquiv : CircuitMaskSample ≃
    {full : (RawCircuitGate → FullHashLift) × CircuitHashRest // FullSourceComplete full.1} where
  toFun source := ⟨circuitGoodHashSource source, fun gate => ⟨_, rfl⟩⟩
  invFun full := decodeFullSource full.1
  left_inv source := by
    simp only [decodeFullSource, circuitGoodHashSource]
    simp only [fullSourceHashPair_good]
    exact circuitMaskHashSplitEquiv.symm_apply_apply source
  right_inv full := by
    apply Subtype.ext
    apply Prod.ext
    · exact decodeFullSource_lifts full.1 full.2
    · simp only [circuitGoodHashSource, decodeFullSource, Equiv.apply_symm_apply]

/-- This change moves both curve randomizers and every selected mask field. -/
def curveSourceMaskEquiv (oldMask newMask : BaseField) (input : AffineInput) :
    CircuitMaskSample ≃ CircuitMaskSample :=
  Equiv.prodCongr
    (Equiv.prodCongr ((curveMaskShiftEquiv oldMask input).trans
      (curveMaskShiftEquiv newMask input).symm) (Equiv.refl _)) (Equiv.refl _)

/-- The complete-fiber change keeps the full selected public request. -/
theorem curveSourceMaskEquiv_garble (oldKey oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (resultEq : oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2)) :
    circuitMaskSampleGarble newKey newMask rows input (curveSourceMaskEquiv oldMask newMask input source) =
      circuitMaskSampleGarble oldKey oldMask rows input source := by
  have curve : curveMaskSampleGarble newKey newMask input
      (curveSourceMaskEquiv oldMask newMask input source).1 =
        curveMaskSampleGarble oldKey oldMask input source.1 := by
    simp only [curveMaskSampleGarble, curveSourceMaskEquiv, Equiv.prodCongr_apply,
      Prod.map, Equiv.refl_apply, Equiv.trans_apply, curveMaskViewEquiv, Equiv.apply_symm_apply]
    exact congrArg (fun target => curveSampleViewEquiv.symm
      ((curveMaskFiberEquiv input target (curveMaskShiftEquiv oldMask input source.1.1)).1, source.1.2)) resultEq.symm
  exact congrArg (fun value : CurvePublicSample =>
    ({curve := value, points := (circuitMaskSampleGarble oldKey oldMask rows input source).points} : PublicSample)) curve

private def extendCompleteEquiv {A : Type*} (complete : A → Prop)
    (change : {value // complete value} ≃ {value // complete value}) : A ≃ A where
  toFun value := if h : complete value then (change ⟨value, h⟩).1 else value
  invFun value := if h : complete value then (change.symm ⟨value, h⟩).1 else value
  left_inv value := by
    by_cases h : complete value
    · simp only [dif_pos h, dif_pos (change ⟨value, h⟩).2]
      exact congrArg Subtype.val (change.symm_apply_apply ⟨value, h⟩)
    · simp only [dif_neg h]
  right_inv value := by
    by_cases h : complete value
    · simp only [dif_pos h, dif_pos (change.symm ⟨value, h⟩).2]
      exact congrArg Subtype.val (change.apply_symm_apply ⟨value, h⟩)
    · simp only [dif_neg h]

/-- The full-source change leaves incomplete tags unchanged. -/
def fullCurveMaskEquiv (oldMask newMask : BaseField) (input : AffineInput) :
    ((RawCircuitGate → FullHashLift) × CircuitHashRest) ≃
      ((RawCircuitGate → FullHashLift) × CircuitHashRest) :=
  extendCompleteEquiv (fun full => FullSourceComplete full.1)
    (completeCircuitSourceEquiv.symm.trans
      ((curveSourceMaskEquiv oldMask newMask input).trans completeCircuitSourceEquiv))

/-- Every full source remains uniform under the complete-fiber change. -/
theorem fullCurveMaskEquiv_uniform (oldMask newMask : BaseField) (input : AffineInput) :
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).map
      (fullCurveMaskEquiv oldMask newMask input) =
        PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest) :=
  map_uniformOfFintype_equivBetween _

/-- A complete source follows the exact field and quotient change. -/
theorem fullCurveMaskEquiv_complete (oldMask newMask : BaseField) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1) :
    fullCurveMaskEquiv oldMask newMask input full =
      circuitGoodHashSource (curveSourceMaskEquiv oldMask newMask input (decodeFullSource full)) := by
  simp only [fullCurveMaskEquiv, extendCompleteEquiv, Equiv.coe_fn_mk, dif_pos complete,
    Equiv.trans_apply, completeCircuitSourceEquiv]
  rfl

/-- An incomplete source keeps its original full tag and randomizers. -/
theorem fullCurveMaskEquiv_incomplete (oldMask newMask : BaseField) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (incomplete : ¬ FullSourceComplete full.1) :
    fullCurveMaskEquiv oldMask newMask input full = full := by
  simp only [fullCurveMaskEquiv, extendCompleteEquiv, Equiv.coe_fn_mk, dif_neg incomplete]

/-- The full-source change preserves the complete-source predicate. -/
theorem fullCurveMaskEquiv_complete_iff (oldMask newMask : BaseField) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    FullSourceComplete (fullCurveMaskEquiv oldMask newMask input full).1 ↔ FullSourceComplete full.1 := by
  by_cases complete : FullSourceComplete full.1
  · rw [fullCurveMaskEquiv_complete oldMask newMask input full complete]
    exact iff_of_true (fun gate => ⟨_, rfl⟩) complete
  · rw [fullCurveMaskEquiv_incomplete oldMask newMask input full complete]

/-- The decoder follows the complete field and quotient permutation. -/
theorem fullCurveMaskEquiv_decode (oldMask newMask : BaseField) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1) :
    decodeFullSource (fullCurveMaskEquiv oldMask newMask input full) =
      curveSourceMaskEquiv oldMask newMask input (decodeFullSource full) := by
  rw [fullCurveMaskEquiv_complete oldMask newMask input full complete]
  exact completeCircuitSourceEquiv.left_inv _

/-- The full-source permutation preserves the complete selected public request. -/
theorem fullCurveMaskEquiv_garble (oldKey oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1)
    (resultEq : oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2)) :
    circuitMaskSampleGarble newKey newMask rows input
      (decodeFullSource (fullCurveMaskEquiv oldMask newMask input full)) =
        circuitMaskSampleGarble oldKey oldMask rows input (decodeFullSource full) := by
  rw [fullCurveMaskEquiv_decode oldMask newMask input full complete]
  exact curveSourceMaskEquiv_garble oldKey oldMask newKey newMask rows input _ resultEq

/-- The source permutation keeps every quotient coordinate. -/
theorem curveSourceMaskEquiv_quotients (oldMask newMask : BaseField) (input : AffineInput)
    (source : CircuitMaskSample) :
    circuitSourceQuotients (curveSourceMaskEquiv oldMask newMask input source) =
      circuitSourceQuotients source := rfl

/-- The source permutation keeps every ciphertext coordinate. -/
theorem curveSourceMaskEquiv_ciphertexts (oldMask newMask : BaseField) (input : AffineInput)
    (source : CircuitMaskSample) :
    sourceCiphertexts (curveSourceMaskEquiv oldMask newMask input source) = sourceCiphertexts source := rfl

/-- The source permutation moves both curve randomizers with the mask. -/
theorem curveSourceMaskEquiv_randomizers (oldMask newMask : BaseField) (input : AffineInput)
    (source : CircuitMaskSample) :
    (curveSourceMaskEquiv oldMask newMask input source).1.1.1 0 = oldMask + source.1.1.1 0 - newMask ∧
    (curveSourceMaskEquiv oldMask newMask input source).1.1.1 1 = -oldMask + source.1.1.1 1 + newMask := by
  constructor <;> simp [curveSourceMaskEquiv, curveMaskShiftEquiv, Equiv.addLeft] <;> ring

/-- The off-curve mask change keeps the selected result and every public request. -/
theorem fullCurveMaskEquiv_offCurve [FieldCertificate]
    (oldKey oldMask hiddenKey : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (invalid : ¬ OnCurve input)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1) :
    let newMask := (oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) - hiddenKey) /
      (input.x ^ 3 + 3 - input.y ^ 2)
    circuitMaskSampleGarble hiddenKey newMask rows input
      (decodeFullSource (fullCurveMaskEquiv oldMask newMask input full)) =
        circuitMaskSampleGarble oldKey oldMask rows input (decodeFullSource full) := by
  dsimp only
  apply fullCurveMaskEquiv_garble oldKey oldMask hiddenKey _ rows input full complete
  rw [div_mul_cancel₀ _ (curveResidual_ne_zero input invalid)]
  ring

/-- The full-source permutation preserves the table seen before the input choice. -/
theorem fullCurveMaskEquiv_table (oldKey oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (complete : FullSourceComplete full.1)
    (resultEq : oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2)) :
    circuitMaskSourceTable newKey newMask rows
      (decodeFullSource (fullCurveMaskEquiv oldMask newMask input full)) =
        circuitMaskSourceTable oldKey oldMask rows (decodeFullSource full) := by
  unfold circuitMaskSourceTable
  rw [circuitMaskSampleGarble_table_input newKey newMask rows _ ⟨0, 0⟩ input,
    circuitMaskSampleGarble_table_input oldKey oldMask rows _ ⟨0, 0⟩ input]
  exact congrArg publicMaskTable
    (fullCurveMaskEquiv_garble oldKey oldMask newKey newMask rows input full complete resultEq)

/-- The adaptive prefix weight follows the exact full-source change of variables. -/
theorem fullCurveMaskEquiv_weighted (oldKey oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (choose : Pipeline.Table → ℝ≥0∞)
    (weight : ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞)
    (resultEq : oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2)) :
    (∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable oldKey oldMask rows (decodeFullSource full)) *
          weight (fullCurveMaskEquiv oldMask newMask input full) else 0) =
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable newKey newMask rows (decodeFullSource full)) * weight full else 0 := by
  have reindex := (fullCurveMaskEquiv oldMask newMask input).tsum_eq
    (fun full => (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable newKey newMask rows (decodeFullSource full)) * weight full else 0)
  apply Eq.trans _ reindex
  apply tsum_congr
  intro full
  simp only [PMF.uniformOfFintype_apply, fullCurveMaskEquiv_complete_iff]
  by_cases complete : FullSourceComplete full.1
  · rw [if_pos complete, if_pos complete,
      fullCurveMaskEquiv_table oldKey oldMask newKey newMask rows input full complete resultEq]
  · simp only [if_neg complete]

end
end Kriterion.ArgoMAC.Security
