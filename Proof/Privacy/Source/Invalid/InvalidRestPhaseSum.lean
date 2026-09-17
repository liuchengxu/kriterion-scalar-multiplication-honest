import Proof.Privacy.Source.Invalid.InvalidSourcePhaseMass
import Proof.Privacy.Source.FullSourceRestTransport
import Proof.Shared.SourcePhaseSum
import Proof.Privacy.Source.Invalid.InvalidGhostNormalization

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This weight retains the actual missing-query source prefix. -/
def invalidRetainedPhaseWeight [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) (retained : MaskRetainedTape)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) : ℝ≥0∞ :=
    ∑' choice, (gateSourceChoose adversary parameter auxiliary
      (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) choice *
      retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback retained full choice output

set_option maxRecDepth 4096 in
/-- The restored retained weight has the exact invalid event and phase factors. -/
theorem invalidRetainedPhaseWeight_event [FieldCertificate] [GroupCertificate] {Aux : Type}
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
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    invalidRetainedPhaseWeight adversary parameter auxiliary scalar fallback
      (table, selected, before, labels, decision, after)
      (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))
      (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after) ∧
      sample ∈ invalidTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
        table selected.1 key (sourcePrefixReference referenceBefore rest) before after tag then 1 else 0) := by
  unfold invalidRetainedPhaseWeight
  rw [← retainedFullTable_prefixTable scalar rest sample tag]
  exact invalidRetainedMiss_phase_mass adversary parameter auxiliary scalar rest sample tag fallback table
    referenceBefore referenceAfter selected labels decision before after key invalid bits mac firstCompatible secondCompatible

set_option maxRecDepth 4096 in
/-- The complete retained sum equals the normalized invalid event sum. -/
def invalidRetainedPhaseWeight_sum [FieldCertificate] [GroupCertificate]
    [Fintype MaskRetainedTape]
    [Fintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  exact (fullSourceRest_retained_weighted_eq witness
    (invalidRetainedPhaseWeight adversary parameter auxiliary scalar fallback
      (table, selected, before, labels, decision, after))).trans
    (source_phase_sum_event (PMF.uniformOfFintype GarblingSourceRest)
      (PMF.uniformOfFintype FullCircuitSource)
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) _
      (fun rest => rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (before ++ after))
      (fun rest tag => invalidTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
        table selected.1 key (sourcePrefixReference referenceBefore rest) before after tag) _
      (fun rest tag sample => invalidRetainedPhaseWeight_event adversary parameter auxiliary scalar
        rest sample tag fallback table referenceBefore referenceAfter selected labels decision before after key
        invalid bits mac firstCompatible secondCompatible))

attribute [local instance] publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

set_option maxRecDepth 4096 in
/-- The retained phase weight is the exact missing-query total. -/
theorem invalidRetainedPhaseWeight_total [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) (retained : MaskRetainedTape) :
    retainedMissTotal adversary parameter auxiliary scalar fallback output retained =
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        invalidRetainedPhaseWeight adversary parameter auxiliary scalar fallback output retained full := by
  unfold retainedMissTotal
  apply tsum_congr
  intro full
  apply congrArg (_ * ·)
  rfl

set_option maxRecDepth 4096 in
/-- The normalized invalid ghost mass is bounded by the actual restored event sum. -/
def invalidGhostGood_rest_event_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) := by
  have total := fullGateGhostGood_mass_le_retainedMiss adversary parameter auxiliary scalar witness fallback
    (table, selected, before, labels, decision, after) invalid
  simp_rw [invalidRetainedPhaseWeight_total] at total
  exact total.trans_eq (invalidRetainedPhaseWeight_sum adversary parameter auxiliary scalar witness fallback table
    referenceBefore referenceAfter selected labels decision before after key invalid bits mac firstCompatible secondCompatible)

end
end Kriterion.ArgoMAC.Security
