import Proof.Privacy.Source.Valid.ValidPrefixEvent
import Proof.Privacy.Source.Invalid.InvalidSourcePhaseEvent

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The restored retained event is the exact valid tag event. -/
theorem validTagGoodEvent_iff_retained [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (tag : FullCircuitSource) (table : Pipeline.Table) (input : AffineInput)
    (key : InputMacKey) (reference : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (labels : Garbling.Labels)
    (valid : OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac) :
    sample ∈ validTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
      table input key (sourcePrefixReference reference rest) before after tag ↔
    FullSourceComplete tag.1 ∧
    ¬rawSourceBad
      (simulatorSourceEquiv ((maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2,
        defaultSimulatorCoin.tableSample)).1
      (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)) input before ∧
    circuitMaskSourceTable
      (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
      (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
      (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))))
      (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)) = table ∧
    OracleTranscriptCompatible idealOracleHandler
      (initialSourceOracle (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2) before ∧
    sourceInputLabels (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2 input = labels ∧
    OracleTranscriptCompatible idealOracleHandler
      (programSelectedGateView
        (transcriptFinalState idealOracleHandler
          (initialSourceOracle (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2) before)
        input (sourceInputLabels (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2 input).inputMac
        (selectedGateView
          (circuitMaskSampleGarble
            (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
            (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
            (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))) input
            (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2))) input)) after := by
  rw [rawSourceBad_oracleKey, retainedSourceRows_oracleKey, sharedCircuitHashRest_oracleKey]
  exact validTagGoodEvent_iff_source rest (outputKeys construction scalar rest.reference.offsets)
    table input key reference before after tag labels valid bits mac sample

private theorem component_phase_eq {actual value factor : ℝ≥0∞}
    {complete bad event normalized : Prop}
    [Decidable complete] [Decidable bad] [Decidable event] [Decidable normalized]
    (component : actual = if ¬complete ∨ bad then 0 else value)
    (phase : value = factor * (if event then 1 else 0))
    (events : (complete ∧ ¬bad ∧ event) ↔ normalized) :
    actual = factor * (if normalized then 1 else 0) := by
  rw [component, phase]
  simp only [← events]
  by_cases full : complete <;> by_cases failed : bad <;> simp [full, failed]

set_option maxRecDepth 4096 in
/-- The valid source component has the common phase factors and its exact tag event. -/
def validPrefixComponent_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :=
  component_phase_eq
    (fullGatePrefixGood_component adversary parameter auxiliary scalar
      (garblingOracleKeyEquiv.symm (sample, rest)) tag fallback
      (table, selected, before, labels, decision, after))
    (gateSourcePhases_mass_factor_at adversary parameter auxiliary
      (circuitMaskSourceTable
        (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
        (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))))
        (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)))
      table (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.2
      (fun input => selectedGateView
        (circuitMaskSampleGarble
          (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
          (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
          (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))) input
          (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2))) input)
      referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible)
    (validTagGoodEvent_iff_retained scalar rest sample tag table selected.1 key referenceBefore before after labels
      valid bits mac).symm

end
end Kriterion.ArgoMAC.Security
