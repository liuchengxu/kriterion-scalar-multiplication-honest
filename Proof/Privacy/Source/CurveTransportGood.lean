import Proof.Privacy.Source.CompleteCurveTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The curve change keeps every point offset, for any label keys. -/
theorem curveSourceMask_pointOffset (oldMask newMask : BaseField) (input : AffineInput)
    (source : CircuitMaskSample) (pointKey curveKey newPointKey newCurveKey : InputMacKey)
    (row : Fin FieldMacToECMac.outputMacCount) (family : PointGateFamily)
    (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    (sourceGatePrescription (curveSourceMaskEquiv oldMask newMask input source) newPointKey newCurveKey
      (fun gate => goodHashLiftSource
        ((circuitMaskHashSplitEquiv (curveSourceMaskEquiv oldMask newMask input source)).1 gate))
      (pointRawGate row family bit)).offset slot =
    (sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (pointRawGate row family bit)).offset slot := by
  rcases family with family | (family | family) <;> cases slot <;> rfl

/-- The curve change preserves offset injection without preserving inactive curve slopes. -/
theorem curveSourceMask_offsets (oldMask newMask : BaseField) (input : AffineInput)
    (source : CircuitMaskSample) (pointKey curveKey newPointKey newCurveKey : InputMacKey)
    (good : ∀ index, Function.Injective (rawBucketOffset
      (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index)) :
    ∀ index, Function.Injective (rawBucketOffset
      (sourceGatePrescription (curveSourceMaskEquiv oldMask newMask input source) newPointKey newCurveKey
        (fun gate => goodHashLiftSource
          ((circuitMaskHashSplitEquiv (curveSourceMaskEquiv oldMask newMask input source)).1 gate))) index) := by
  let changed := curveSourceMaskEquiv oldMask newMask input source
  let oldLifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
  let newLifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv changed).1 gate)
  intro index first second equal
  obtain ⟨firstRow, rfl⟩ := circuitBucketUse_surjective (circuitGateKey newPointKey newCurveKey)
    (circuitSourceSlope changed) newLifts (circuitSourceTable changed) index first
  obtain ⟨secondRow, rfl⟩ := circuitBucketUse_surjective (circuitGateKey newPointKey newCurveKey)
    (circuitSourceSlope changed) newLifts (circuitSourceTable changed) index second
  apply congrArg
  rcases index with ⟨kind, bit, slot⟩
  cases kind with
  | curve adaptor => exact @Subsingleton.elim (Fin 1) inferInstance firstRow secondRow
  | point coordinate adaptor =>
      apply circuitBucketUse_injective (circuitGateKey pointKey curveKey)
        (circuitSourceSlope source) oldLifts (circuitSourceTable source)
      apply good
      cases coordinate <;> cases adaptor <;>
        try { exact Fin.elim0 firstRow }
      all_goals
        change (sourceGatePrescription source pointKey curveKey oldLifts _).offset slot ^^^ _ =
          (sourceGatePrescription source pointKey curveKey oldLifts _).offset slot ^^^ _
        change (sourceGatePrescription changed newPointKey newCurveKey newLifts _).offset slot ^^^ _ =
          (sourceGatePrescription changed newPointKey newCurveKey newLifts _).offset slot ^^^ _ at equal
        simp only [circuitBucketUse, circuitBucketGate] at equal ⊢
        cases slot <;> exact equal


set_option maxRecDepth 2048 in
/-- The curve change keeps every exposed curve record exactly. -/
theorem curveSourceMask_selectedCurveRecord (oldKey oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (curveKey pointKey newPointKey : InputMacKey)
    (resultEq : oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2))
    (adaptor : Fin 5) (bit : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot)
    (active : rawSlotBranch slot = circuitBucketInputBit input
      (rawLabelBucket (fixedKeyIndex (rawCircuitLocation (.inl (adaptor, bit)))
        (rawCircuitWindow (.inl (adaptor, bit))) slot))) :
    (sourceGatePrescription (curveSourceMaskEquiv oldMask newMask input source) newPointKey curveKey
      (fun gate => goodHashLiftSource
        ((circuitMaskHashSplitEquiv (curveSourceMaskEquiv oldMask newMask input source)).1 gate))
      (.inl (adaptor, bit))).slotRecord slot =
    (sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (.inl (adaptor, bit))).slotRecord slot := by
  have oldActive := active.trans (actualCircuitDirective_bit
    (circuitMaskSampleGarble oldKey oldMask rows input source).curveRequest
    (circuitMaskSampleGarble oldKey oldMask rows input source).pointRequests input
    (curveKey.encodeAffine input) (pointKey.encodeAffine input) (.inl (adaptor, bit)) slot).symm
  have newActive := active.trans (actualCircuitDirective_bit
    (circuitMaskSampleGarble newKey newMask rows input
      (curveSourceMaskEquiv oldMask newMask input source)).curveRequest
    (circuitMaskSampleGarble newKey newMask rows input
      (curveSourceMaskEquiv oldMask newMask input source)).pointRequests input
    (curveKey.encodeAffine input) (newPointKey.encodeAffine input) (.inl (adaptor, bit)) slot).symm
  rw [← circuitMaskDirective_record_eq_raw newKey newMask rows input
    (curveSourceMaskEquiv oldMask newMask input source) curveKey newPointKey _ slot newActive,
    ← circuitMaskDirective_record_eq_raw oldKey oldMask rows input source curveKey pointKey _ slot oldActive]
  simp only [actualCircuitDirective]
  rw [curveSourceMaskEquiv_garble oldKey oldMask newKey newMask rows input source resultEq]

/-- An invalid good source remains good under the complete curve mask change. -/
theorem curveSourceMask_good_invalid (coin : SimulatorCoin) (oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (source : CircuitMaskSample)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (invalid : ¬ OnCurve input)
    (resultEq : coin.bridgeKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2))
    (good : ¬ rawSourceBad coin source input history) :
    ¬ rawSourceBad {coin with bridgeKey := newKey}
      (curveSourceMaskEquiv oldMask newMask input source) input history := by
  classical
  simp only [rawSourceBad, not_or, not_not]
  constructor
  · exact curveSourceMask_offsets oldMask newMask input source _ _ _ _
      (rawSourceGood_offsets coin source input history good)
  · intro gate slot active exposed
    rcases exposed with valid | ⟨adaptor, bit, rfl⟩
    · exact (invalid valid).elim
    · rw [curveSourceMask_selectedCurveRecord coin.bridgeKey oldMask newKey newMask rows input source
        coin.inputKey _ _ resultEq adaptor bit slot active]
      exact rawSourceGood_fresh coin source input history good (.inl (adaptor, bit)) slot
        active (Or.inr ⟨adaptor, bit, rfl⟩)

/-- A complete full source keeps its invalid good predicate after the ghost change. -/
theorem fullCurveMask_good_invalid (coin : SimulatorCoin) (oldMask newKey newMask : BaseField)
    (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete full.1) (invalid : ¬ OnCurve input)
    (resultEq : coin.bridgeKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
      newKey + newMask * (input.x ^ 3 + 3 - input.y ^ 2))
    (good : ¬ rawSourceBad coin (decodeFullSource full) input history) :
    ¬ rawSourceBad {coin with bridgeKey := newKey}
      (decodeFullSource (fullCurveMaskEquiv oldMask newMask input full)) input history := by
  rw [fullCurveMaskEquiv_decode oldMask newMask input full complete]
  exact curveSourceMask_good_invalid coin oldMask newKey newMask rows input (decodeFullSource full)
    history invalid resultEq good

end
end Kriterion.ArgoMAC.Security
