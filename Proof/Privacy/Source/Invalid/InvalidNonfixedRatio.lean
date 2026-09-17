import Proof.Privacy.Source.GoodLinkedCurveNonfixed
import Proof.Privacy.Source.NonfixedSourceMass
import Proof.Privacy.Source.LinkedTagRealSum
import Proof.Privacy.Bounds.AdaptiveLossAccounting
import Proof.Privacy.Source.Invalid.InvalidSourceNormalization

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  instFintypeEncQueryDomainOfBlock bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The two relative exclusions use the full transcript budget once. -/
theorem invalidRelativeLoss_budget (budget length size : Nat) (bounded : length ≤ budget) :
    1 - (((186 * budget + 508 : Nat) : ℝ≥0∞) / size) ≤
      (1 - ((4 * budget : Nat) : ℝ≥0∞) / size) *
      (1 - (((182 * length : Nat) : ℝ≥0∞) / size + 508 / size)) := by
  have split : (((186 * budget + 508 : Nat) : ℝ≥0∞) / size) =
      ((4 * budget : Nat) : ℝ≥0∞) / size +
        (((182 * budget : Nat) : ℝ≥0∞) / size + 508 / size) := by
    rw [show 186 * budget + 508 = 4 * budget + (182 * budget + 508) by omega]
    simp only [Nat.cast_add, ENNReal.add_div, Nat.cast_ofNat]
  rw [split]
  apply (relativeLoss_product _ _).trans
  apply mul_le_mul_right
  apply tsub_le_tsub_left
  apply add_le_add_left
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 182 bounded)) _

/-- A constant relative factor commutes with a guarded average. -/
private theorem guarded_constant_factor {Sample : Type*} (samples : PMF Sample)
    (kept : Sample → Prop) (label factor value : ℝ≥0∞) :
    (∑' sample, samples sample * if kept sample then label * (factor * value) else 0) =
      factor * ∑' sample, samples sample * if kept sample then label * value else 0 := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro sample
  by_cases keep : kept sample
  · simp only [if_pos keep]
    ac_rfl
  · simp only [if_neg keep, mul_zero]

/-- This update fixes the reference form before the source rest is substituted. -/
def nonfixedSourceReference (randomness : Garbling.Randomness)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) : Garbling.Randomness :=
  {randomness with encPRFOracle := enc, hashOracle := hash}

/-- The Enc and hash average uses one combined relative loss. -/
theorem nonfixedRelative_mass_ge [Fintype Block] [Fintype BaseField]
    (randomness : Garbling.Randomness) (history : List (Sigma Garbling.oracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle (encOracleTranscriptRecords history))
    (budget : Nat) (bounded : history.length ≤ budget) (label value result : ℝ≥0∞)
    (bound : ((1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords history)) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if NonFixedTranscriptCompatible {randomness with hashOracle := hash} history then
          label * ((1 - (((182 * history.length : Nat) : ℝ≥0∞) / Fintype.card Block +
            508 / Fintype.card Block)) * value) else 0) ≤ result) :
    (1 - (((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block)) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
          (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          if NonFixedTranscriptCompatible (nonfixedSourceReference randomness enc hash) history
            then label * value else 0) ≤ result := by
  unfold nonfixedSourceReference
  have average := nonfixedEncHash_weighted_eq randomness history reference (fun _ => label * value)
  rw [← average]
  apply le_trans _ bound
  rw [guarded_constant_factor]
  have loss := invalidRelativeLoss_budget budget history.length (Fintype.card Block) bounded
  apply le_trans (mul_le_mul_left loss _)
  exact le_of_eq (by ac_rfl)

private theorem uniform_mass_nonempty {Sample : Type*} [Fintype Sample]
    (first second : Nonempty Sample) (event : Set Sample) :
    (@PMF.uniformOfFintype Sample _ first).toOuterMeasure event =
      (@PMF.uniformOfFintype Sample _ second).toOuterMeasure event := by
  cases Subsingleton.elim first second
  rfl

/-- This mass keeps the selected labels, fixed prefix, and curve-only programmed replies. -/
def invalidFixedProgrammedMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : SimulatorState) (after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ℝ≥0∞ :=
  (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
    (fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map fun oracle =>
        programGateSchedule (let current := state; {current with fixedOracle := oracle.1})
          (invalidSourceSchedule rest outputKeys input key tag)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})

set_option maxRecDepth 4096 in
/-- A complete good source needs only the nonfixed reference replies. -/
theorem fullSourceGood_curve_nonfixed_combined_mass_ge
    [Fintype Block] [Fintype BaseField]
    (coin : SimulatorCoin) (curveKey : InputMacKey) (bridgeKey : BaseField)
    (keyEq : coin.inputKey = curveKey) (bridgeEq : coin.bridgeKey = bridgeKey)
    (mask : NonZeroBase) (rows : FieldMacToECMac.Rows)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (lifts : RawCircuitGate → FullHashLift) (liftEq : full.1 = lifts)
    (input : AffineInput) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (randomness : Garbling.Randomness)
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (r1 r2 : BaseField)
    (randomizers : CircuitSourceRandomizers (decodeFullSource full) pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField (decodeFullSource full) gate = ((full.1 gate).val : BaseField))
    (complete : FullSourceComplete full.1)
    (good : ¬ rawSourceBad coin (decodeFullSource full) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : coin.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle
      (encOracleTranscriptRecords (before ++ after)))
    (budget : Nat) (small : budget < 2 ^ 100) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    (1 - (((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block)) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
          (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          if NonFixedTranscriptCompatible (nonfixedSourceReference randomness enc hash) (before ++ after) then
            (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
              (fixedTranscriptFactor state.fixedTranscript *
                ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
                  programGateSchedule {state with fixedOracle := oracle.1}
                    ((circuitMaskSampleGarble bridgeKey mask.value rows input (decodeFullSource full)).curveRequest.schedule input (curveKey.encodeAffine input)))).toOuterMeasure
                  {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
            else 0) ≤
    (fullSourceTagDensity (lifts, sourceCiphertexts (decodeFullSource full)))⁻¹ *
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        (decodeFullSource full) lifts (inputSelectedLabelBit input) (inputMacCoordinateEquiv (curveKey.encodeAffine input)) (before ++ after)) := by
  rw [← keyEq, ← bridgeEq, ← liftEq]
  have bound := fullSourceGood_curve_nonfixed_mass_ge coin mask rows full input state before after
    randomness outputKeys pointRandomness r1 r2 randomizers residues complete good members miss budget small lengthBound
  dsimp only at bound
  have combined := nonfixedRelative_mass_ge randomness (before ++ after) reference budget lengthBound
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹
    (fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
        programGateSchedule {state with fixedOracle := oracle.1}
          ((circuitMaskSampleGarble coin.bridgeKey mask.value rows input (decodeFullSource full)).curveRequest.schedule
            input (coin.inputKey.encodeAffine input)))).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
    _ bound
  exact combined

end
end Kriterion.ArgoMAC.Security
