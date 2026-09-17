import Proof.Privacy.Source.Valid.ValidPrefixEvent
import Proof.Privacy.Source.FullCircuitSourceDensity
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  fixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private theorem weighted_guard {condition : Prop} [Decidable condition]
    (density event value result : ℝ≥0∞)
    (eventEq : event = if condition then value else 0)
    (valueEq : density * value = result) :
    density * event = if condition then result else 0 := by
  rw [eventEq]
  split_ifs
  · exact valueEq
  · exact mul_zero _

private def validProgrammedBaseMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (state : SimulatorState)
    (after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ℝ≥0∞ :=
  (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
    (fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => programGateSchedule {state with fixedOracle := oracle.1}
          (validSourceSchedule rest outputKeys input key tag))).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})

private theorem validProgrammed_formula_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (state : SimulatorState)
    (after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    (PMF.uniformOfFintype FullCircuitSource) tag *
      validProgrammedBaseMass rest outputKeys input key state after tag =
    validProgrammedTagMass rest outputKeys input key state after tag := by
  rw [fullCircuitSource_uniform_mass, validProgrammedTagMass, validProgrammedBaseMass]
  have reorder (p c f m : ENNReal) : p * (c * (f * m)) = c * (p * f * m) := by ac_rfl
  exact reorder _ _ _ _

private theorem validProgrammed_base_eq [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
          (fun oracle => programGateSchedule
            {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
            (validSourceSchedule rest outputKeys input key tag))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) =
      validProgrammedBaseMass rest outputKeys input key
        (transcriptFinalState idealOracleHandler initial before) after tag := by
  unfold validProgrammedBaseMass
  apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
  apply congrArg (fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript * ·)
  apply congrArg (fun samples : PMF SimulatorState => samples.toOuterMeasure
    {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle
    (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
  funext oracle
  rfl

set_option maxRecDepth 4096 in
/-- The uniform tag weight gives exactly the normalized valid programmed mass. -/
def validTagGoodEvent_weighted_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :=
  weighted_guard ((PMF.uniformOfFintype FullCircuitSource) tag) _ _ _
    (validTagGoodEvent_mass rest outputKeys table input key initial before after tag
      empty enc hash compatible nonfixed)
    ((congrArg (((PMF.uniformOfFintype FullCircuitSource) tag) * ·)
      (validProgrammed_base_eq rest outputKeys input key tag initial before after)).trans
      (validProgrammed_formula_eq rest outputKeys input key
        (transcriptFinalState idealOracleHandler initial before) after tag))

/-- Every retained valid event satisfies both nonfixed transcript segments. -/
theorem validTagGoodEvent_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (member : sample ∈ validTagGoodEvent rest outputKeys table input key initial before after tag) :
    NonFixedTranscriptCompatible rest.reference (before ++ after) := by
  apply (nonFixedTranscriptCompatible_append rest.reference before after).mpr
  refine ⟨idealTranscript_nonfixed {initial with fixedOracle := sample.1} rest.reference before enc hash member.2.2.2.2.1, ?_⟩
  apply idealTranscript_nonfixed _ rest.reference after _ _ member.2.2.2.2.2
  · exact (programGateSchedule_encOracle _ _).trans
      ((idealTranscriptFinal_oracles _ before).1.trans enc)
  · exact (programGateSchedule_hashOracle _ _).trans
      ((idealTranscriptFinal_oracles _ before).2.trans hash)

/-- An incompatible nonfixed transcript has zero valid event mass. -/
theorem validTagGoodEvent_mass_zero [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (tag : FullCircuitSource)
    (enc : initial.encOracle = rest.encPRFOracle) (hash : initial.hashOracle = rest.hashOracle)
    (incompatible : ¬ NonFixedTranscriptCompatible rest.reference (before ++ after)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (validTagGoodEvent rest outputKeys table input key initial before after tag) = 0 := by
  apply (PMF.toOuterMeasure_apply_eq_zero_iff _ _).mpr
  apply Set.disjoint_left.mpr
  intro sample _ member
  exact incompatible (validTagGoodEvent_nonfixed rest outputKeys table input key initial before after tag enc hash sample member)

end
end Kriterion.ArgoMAC.Security
