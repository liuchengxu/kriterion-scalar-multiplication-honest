import Proof.Privacy.Source.Invalid.InvalidSourcePhaseEvent

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 4096 in
/-- The actual restored source keeps the exact invalid tag event. -/
theorem invalidTagGoodEvent_iff_reconstructed [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource) (labels : Garbling.Labels)
    (invalid : ¬ OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :
    let retained := maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))
    let full := (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)
    (FullSourceComplete full.1 ∧
      ¬ rawSourceBad (simulatorSourceEquiv (retained.2.2, defaultSimulatorCoin.tableSample)).1
        (decodeFullSource full) input before ∧
      retained.2.2.1.1 ∉ transcriptHashInputs (before ++ after) ∧
      retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag = table ∧
      OracleTranscriptCompatible idealOracleHandler (initialSourceOracle retained.2.2.2) before ∧
      sourceInputLabels retained.2.2.2 input = labels ∧
      OracleTranscriptCompatible idealOracleHandler
        (programSelectedGateView (transcriptFinalState idealOracleHandler (initialSourceOracle retained.2.2.2) before)
          input (sourceInputLabels retained.2.2.2 input).inputMac
          (selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) input (decodeFullSource full)) input)) after) ↔
      rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) ∧
      sample ∈ invalidTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
        table input key (sourcePrefixReference reference rest) before after tag := by
  dsimp only
  rw [retainedSourceRows_oracleKey, sharedCircuitHashRest_oracleKey, rawSourceBad_oracleKey]
  have event := invalidTagGoodEvent_iff_source rest
    (outputKeys construction scalar rest.reference.offsets) table input key reference before after
    tag labels invalid bits mac sample
  change (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _) ↔ _ ∧ _
  rw [event]
  constructor
  · rintro ⟨complete, good, miss, tableEq, first, same, last⟩
    exact ⟨miss, complete, good, tableEq, first, same, last⟩
  · rintro ⟨miss, complete, good, tableEq, first, same, last⟩
    exact ⟨complete, good, miss, tableEq, first, same, last⟩

private theorem phaseEvent_congr (value factor : ℝ≥0∞) (first second : Prop)
    {firstDec : Decidable first} [Decidable second]
    (law : value = factor * @ite ℝ≥0∞ first firstDec 1 0)
    (same : first ↔ second) : value = factor * if second then 1 else 0 := by
  simpa only [same] using law

set_option maxRecDepth 4096 in
/-- The restored invalid source has the common phase factors and its exact tag event. -/
def invalidRetainedMiss_phase_mass [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :=
  phaseEvent_congr _ _ _ _
    (retainedMissWeight_mass_factor adversary parameter auxiliary scalar
      (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))
      (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)
      fallback (retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag) table
      (retainedFullTable_prefixTable scalar rest sample tag) referenceBefore referenceAfter selected labels
      decision before after firstCompatible secondCompatible)
    (invalidTagGoodEvent_iff_reconstructed scalar rest table selected.1 key referenceBefore before after
      tag labels invalid bits mac sample)

end
end Kriterion.ArgoMAC.Security
