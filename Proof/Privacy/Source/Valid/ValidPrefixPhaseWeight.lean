import Proof.Privacy.Source.Valid.ValidSourcePhaseMass
import Proof.Shared.SourcePhaseSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This weight keeps the original complete source prefix and its bad-event guard. -/
def validPrefixPhaseWeight [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (randomness : Garbling.Randomness) (tag : FullCircuitSource) : ℝ≥0∞ :=
  sourceGoodMass
    (gateSourceChoose adversary parameter auxiliary
      (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1
        (maskRetainedTape randomness).2.2.1.2.value (retainedSourceRows scalar (maskRetainedTape randomness))
        (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)))
      (maskRetainedTape randomness).2.2.2)
    (fun selected => fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback (randomness, tag, selected))
    {selected | fullGatePrefixBad (randomness, tag, selected)} output

/-- The valid weight has the common phase factors and the exact tag event. -/
theorem validPrefixPhaseWeight_event [FieldCertificate] [GroupCertificate] {Aux : Type}
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
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    validPrefixPhaseWeight adversary parameter auxiliary scalar fallback
      (table, selected, before, labels, decision, after) (garblingOracleKeyEquiv.symm (sample, rest)) tag =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if sample ∈ validTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
        table selected.1 key (sourcePrefixReference referenceBefore rest) before after tag then 1 else 0) := by
  exact validPrefixComponent_mass_factor adversary parameter auxiliary scalar rest sample tag fallback table
    referenceBefore referenceAfter selected labels decision before after key valid bits mac firstCompatible secondCompatible

set_option maxRecDepth 4096 in
/-- The restored valid weight sum keeps the common phase factor and exact event mass. -/
def validPrefixPhaseWeight_sum [FieldCertificate] [GroupCertificate]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  letI : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
  exact source_phase_sum_event (PMF.uniformOfFintype GarblingSourceRest)
    (PMF.uniformOfFintype FullCircuitSource)
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) _
    (fun _ => True)
    (fun rest tag => validTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
      table selected.1 key (sourcePrefixReference referenceBefore rest) before after tag)
    (fun rest tag sample => validPrefixPhaseWeight adversary parameter auxiliary scalar fallback
      (table, selected, before, labels, decision, after) (garblingOracleKeyEquiv.symm (sample, rest)) tag)
    (fun rest tag sample => by
      simpa only [true_and] using validPrefixPhaseWeight_event adversary parameter auxiliary scalar rest sample tag
        fallback table referenceBefore referenceAfter selected labels decision before after key
        valid bits mac firstCompatible secondCompatible)

end
end Kriterion.ArgoMAC.Security
