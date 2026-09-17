import Proof.Privacy.Source.Valid.ValidPrefixRestSum
import Proof.Privacy.Source.Valid.ValidEventSourceSum
import Proof.Privacy.Source.Invalid.InvalidEndpointRatio
import Proof.Privacy.Source.GhostSourceGood
import Proof.Privacy.Source.Valid.ValidPrefixWeightExpansion

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The full query budget gives a lower coefficient than the valid transcript length. -/
theorem validSourceRatio_coefficient_le (length budget : Nat) (denominator : ℝ≥0∞)
    (bounded : length ≤ budget) :
    1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / denominator ≤
      1 - ((182 * length : Nat) : ℝ≥0∞) / denominator := by
  apply tsub_le_tsub_left
  gcongr
  omega

private theorem validPhase_relative_bound (ghost prefixMass first second publicMass real factor larger phase : ℝ≥0∞)
    (ghostBound : ghost ≤ prefixMass) (prefixEq : prefixMass = phase * first)
    (sourceBound : larger * second ≤ publicMass) (realEq : real = phase * publicMass)
    (same : first = second) (coefficient : factor ≤ larger) : factor * ghost ≤ real := by
  subst second
  apply phase_relative_bound ghost first publicMass real factor phase
    (ghostBound.trans_eq prefixEq) _ realEq
  exact (mul_le_mul_left coefficient first).trans sourceBound

set_option maxRecDepth 4096 in
private theorem validRestEventMass_eq [FieldCertificate] [GroupCertificate]
    (restFinite : Fintype GarblingSourceRest) (firstTag secondTag : Fintype FullCircuitSource)
    (firstSample secondSample : Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
    (restNonempty : Nonempty GarblingSourceRest)
    (scalar : ScalarField) (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑' rest, @PMF.uniformOfFintype GarblingSourceRest restFinite restNonempty rest *
      ∑' tag, @PMF.uniformOfFintype FullCircuitSource firstTag
        (@instNonemptyProd (RawCircuitGate → FullHashLift) CircuitMaskTables
          (@Pi.instNonempty RawCircuitGate (fun _ => FullHashLift) (fun _ => fullHashLiftNonempty))
          circuitMaskTablesNonempty) tag *
        if (fun _ : GarblingSourceRest => True) rest then
          (@PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
            firstSample (@instNonemptyProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
              (@instNonemptyPermutationOracle _ _) ⟨defaultSimulatorCoin.inputKey⟩)).toOuterMeasure
            ((fun rest tag => validTagGoodEvent rest (outputKeys construction scalar rest.reference.offsets)
              table input key (sourcePrefixReference reference rest) before after tag) rest tag) else 0) =
    ∑' rest, @PMF.uniformOfFintype GarblingSourceRest restFinite restNonempty rest *
      ∑' tag, @PMF.uniformOfFintype FullCircuitSource secondTag
        (@instNonemptyProd (RawCircuitGate → FullHashLift) CircuitMaskTables
          (@Pi.instNonempty RawCircuitGate (fun _ => FullHashLift) (fun _ => fullHashLiftNonempty))
          circuitMaskTablesNonempty) tag *
        (@PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
          secondSample (@instNonemptyProd (PermutationOracle Pipeline.FixedKeyIndex Block) InputMacKey
            (@instNonemptyPermutationOracle _ _) instNonemptyInputMacKey_proof_7)).toOuterMeasure
          (validTagGoodEvent rest (actualSourceOutputKeys scalar rest)
            table input key (sourcePrefixReference reference rest) before after tag) := by
  cases Subsingleton.elim firstTag secondTag
  cases Subsingleton.elim firstSample secondSample
  simp only [ite_true]
  rfl

set_option maxRecDepth 4096 in
/-- The actual valid source satisfies the full transcript ratio. -/
theorem validGhostEndpoint_mass_ge [FieldCertificate] [GroupCertificate]
    [blockFinite : Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (budget : Nat) (small : budget < 2 ^ 100) (bounded : (before ++ after).length ≤ budget) :
    (1 - ((186 * budget + 508 : Nat) : ℝ≥0∞) / Fintype.card Block) *
      sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar.value witness fallback)
        (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin}
        (table, selected, before, labels, decision, after) ≤
      (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction) (randomTape witness)
        Garbling.oracleHandler adversary parameter scalar auxiliary)
        (table, selected, before, labels, decision, after) := by
  have ghost := fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar.value witness fallback
    (table, selected, before, labels, decision, after)
  have prefixEq := fullGatePrefixGood_weight_sum adversary parameter auxiliary scalar.value witness fallback
    (table, selected, before, labels, decision, after)
  have phases := validOriginalWeight_phase_sum adversary parameter auxiliary scalar.value witness fallback table
    referenceBefore referenceAfter selected labels decision before after key valid bits mac firstCompatible secondCompatible
  have source := validEventSourceSum_real_le witness parameter referenceBefore (actualSourceOutputKeys scalar.value)
    table selected.1 key before after firstCompatible valid budget small bounded
  have real := realAdaptiveTranscript_retained_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible
  exact validPhase_relative_bound _ _ _ _ _ _ _ _ _ ghost (prefixEq.trans phases) source real
    (validRestEventMass_eq _ _ _ _ _ ⟨(garblingOracleKeyEquiv witness).2⟩
      scalar.value table selected.1 key referenceBefore before after)
    (validSourceRatio_coefficient_le _ _ _ bounded)

end
end Kriterion.ArgoMAC.Security
