import Proof.Privacy.Source.Invalid.SharedCurvePhaseMass
import Proof.Privacy.Source.Invalid.SharedCurveRestAverage
import Proof.Privacy.Source.SharedRealEndpointPhaseMass
import Proof.Shared.SourcePhaseSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
attribute [local irreducible] PMF.uniformOfFintype sharedCurveSourcePhaseWeight
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curvePhaseSumGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance curvePhaseSumKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curvePhaseSumKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The complete source average keeps both phase factors and the exact guarded pipeline event. -/
theorem sharedCurveSourcePhaseWeight_sum [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (witness : Shared.Randomness) (keys : GarblingSourceRest → OutputKeys)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
            sharedCurveSourcePhaseWeight adversary parameter auxiliary rest (keys rest) sample tag
              (table, selected, before, labels, decision, after)) =
    (((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after)) *
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        sharedCurveRestEventMass rest (keys rest) table selected.1 key
          referenceBefore before after := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  have law := source_phase_sum_event (PMF.uniformOfFintype GarblingSourceRest)
    (PMF.uniformOfFintype FullCircuitSource)
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) _
    (fun _ => True)
    (fun rest tag => sharedCurveTagEvent rest (keys rest) table selected.1 key
      (sharedSourcePrefixReference referenceBefore rest) before after tag)
    (fun rest tag sample => sharedCurveSourcePhaseWeight adversary parameter auxiliary rest (keys rest) sample tag
      (table, selected, before, labels, decision, after))
    (fun rest tag sample => by
      simpa only [true_and] using sharedCurveSourcePhaseWeight_event adversary parameter auxiliary rest (keys rest)
        sample tag table referenceBefore referenceAfter selected labels decision before after key invalid bits mac
        firstCompatible secondCompatible)
  simpa only [if_true, sharedCurveRestEventMass] using law

/-- The complete guarded curve source has one numerical relative loss. -/
theorem sharedCurveSourcePhaseWeight_sum_real_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar)
    (witness : Shared.Randomness) (table : Pipeline.Table)
    (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (invalid : ¬ OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (encReference : PermutationTranscriptMatches referenceBefore.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (1 - ((54691280 + 368 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
            (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
              sharedCurveSourcePhaseWeight adversary parameter auxiliary rest
                (outputKeys construction scalar.value rest.reference.offsets) sample tag
                (table, selected, before, labels, decision, after)) ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
          (table, selected, before, labels, decision, after) := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedCurveSourcePhaseWeight_sum adversary parameter auxiliary witness
    (fun rest => outputKeys construction scalar.value rest.reference.offsets) table referenceBefore referenceAfter
    selected labels decision before after key invalid bits mac firstCompatible secondCompatible]
  rw [sharedRealAdaptiveTranscript_retained_factor adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible]
  rw [mul_left_comm]
  apply mul_le_mul_right
  rw [sharedCurveRestEventMass_average
    (fun rest => outputKeys construction scalar.value rest.reference.offsets) (fun _ _ _ => rfl)]
  apply le_trans ?_ (sharedLinkedGlobalSourceMass_real_le witness parameter
    (fun rest => outputKeys construction scalar.value rest.reference.offsets) (fun _ _ _ => rfl)
    table selected.1 (key.encodeAffine selected.1) (before ++ after))
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rest
  rw [mul_left_comm]
  exact mul_le_mul_right (sharedCurveRestEventMass_normalized_ratio rest
    (outputKeys construction scalar.value rest.reference.offsets) table selected.1 key referenceBefore before after
    firstCompatible encReference budget small lengthBound) _

end
end Kriterion.ArgoMAC.Security
