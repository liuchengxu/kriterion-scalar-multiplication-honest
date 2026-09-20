import Proof.Privacy.Source.Valid.SharedPipelinePhaseGuard
import Proof.Privacy.Source.Valid.SharedPipelineGlobalEventRatio
import Proof.Shared.SourcePhaseSum
import Proof.Privacy.Source.Valid.SharedPipelineEndpointRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] PMF.uniformOfFintype sharedPipelinePhaseWeight
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelinePhaseSumGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
local instance pipelinePhaseSumKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelinePhaseSumKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The prefix event uses exactly the complete nonfixed compatibility guard. -/
theorem sharedPipelinePrefixEventMass_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (reference : Shared.Simulator.OracleState) (rest : GarblingSourceRest) (keys : OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before) :
    sharedPipelinePrefixEventMass rest keys table input key (sharedSourcePrefixReference reference rest) before after =
      if SharedNonFixedTranscriptCompatible (reference.fixedOracle, rest.encPRFOracle, rest.hashOracle)
          (before ++ after) then
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
            (sharedPipelineTagEvent rest keys table input key (sharedSourcePrefixReference reference rest) before after tag)
      else 0 := by
  unfold sharedPipelinePrefixEventMass
  by_cases nonfixed : SharedNonFixedTranscriptCompatible
      (reference.fixedOracle, rest.encPRFOracle, rest.hashOracle) (before ++ after)
  · have split := (sharedNonFixedTranscriptCompatible_append _ _ _).mp nonfixed
    rw [if_pos ⟨sharedSourcePrefixReference_compatible reference rest before compatible split.1,
      split.2, nonfixed⟩, if_pos nonfixed]
  · rw [if_neg (fun guard => nonfixed guard.2.2), if_neg nonfixed]

/-- The complete source average keeps both phase factors and the exact guarded pipeline event. -/
theorem sharedPipelinePhaseWeight_sum [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (witness : Shared.Randomness) (keys : GarblingSourceRest → OutputKeys)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
            sharedPipelinePhaseWeight adversary parameter auxiliary rest (keys rest) sample tag
              (table, selected, before, labels, decision, after)) =
    (((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after)) *
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        sharedPipelinePrefixEventMass rest (keys rest) table selected.1 key
          (sharedSourcePrefixReference referenceBefore rest) before after := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  have law := source_phase_sum_event (PMF.uniformOfFintype GarblingSourceRest)
    (PMF.uniformOfFintype FullCircuitSource)
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) _
    (fun rest => SharedNonFixedTranscriptCompatible
      (referenceBefore.fixedOracle, rest.encPRFOracle, rest.hashOracle) (before ++ after))
    (fun rest tag => sharedPipelineTagEvent rest (keys rest) table selected.1 key
      (sharedSourcePrefixReference referenceBefore rest) before after tag)
    (fun rest tag sample => sharedPipelinePhaseWeight adversary parameter auxiliary rest (keys rest) sample tag
      (table, selected, before, labels, decision, after))
    (fun rest tag sample => sharedPipelinePhaseWeight_guarded_factor adversary parameter auxiliary rest (keys rest)
      sample tag table referenceBefore referenceAfter selected labels decision before after key valid bits mac
      firstCompatible secondCompatible)
  apply law.trans
  congr 1
  apply tsum_congr
  intro rest
  congr 1
  rw [sharedPipelinePrefixEventMass_eq referenceBefore rest (keys rest) table selected.1 key before after firstCompatible]
  split <;> simp_all only [if_pos, if_neg, mul_zero, tsum_zero]

/-- The averaged guarded pipeline source is bounded by the complete real transcript mass. -/
theorem sharedPipelinePhaseWeight_sum_real_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar)
    (witness : Shared.Randomness) (table : Pipeline.Table)
    (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : (before ++ after).length ≤ budget) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (1 - ((54690772 + 364 * budget : Nat) : ENNReal) / (2 : ENNReal) ^ 128) *
      (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
          ∑' sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey,
            (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
              sharedPipelinePhaseWeight adversary parameter auxiliary rest
                (outputKeys construction scalar.value rest.reference.offsets) sample tag
                (table, selected, before, labels, decision, after)) ≤
      (realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary)
          (table, selected, before, labels, decision, after) := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  rw [sharedPipelinePhaseWeight_sum adversary parameter auxiliary witness
    (fun rest => outputKeys construction scalar.value rest.reference.offsets) table referenceBefore referenceAfter
    selected labels decision before after key valid bits mac firstCompatible secondCompatible]
  exact sharedPipelineEndpoint_mass_ge adversary parameter auxiliary scalar witness table
    referenceBefore referenceAfter selected labels decision before after key bits mac firstCompatible secondCompatible
    (sharedSourcePrefixReference referenceBefore) (fun _ => rfl)
    (sharedSourcePrefixReference_invariant referenceBefore) budget small lengthBound

end
end Kriterion.ArgoMAC.Security
