import Proof.Privacy.Source.Valid.SharedPipelineSourceEvent
import Proof.Privacy.Source.SharedGateSourceEndpointMass
import Proof.Privacy.Source.SharedGateSourceGoodMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This weight keeps the actual shared prefix and complete pipeline guard. -/
def sharedPipelinePhaseWeight [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (output : SharedFullGateTranscript adversary.State) : ENNReal :=
  let table := retainedFullTable rest keys tag
  let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
  sourceGoodMass (sharedGateSourceChoose adversary parameter auxiliary table data)
    (fun selected => sharedGateSourceObserve adversary parameter auxiliary table selected
      (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
        (rowsForOutputKeys keys rest.algebraic.point.pointRandomness) selected.1 (retainedFullSource rest tag))
        selected.1) data)
    {selected | ¬ SharedPipelineTagGood rest keys table selected.1 sample.2
      (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) selected.2.2.2) tag} output

/-- The guarded pipeline mass keeps both common phase factors and the exact source event. -/
theorem sharedPipelinePhaseWeight_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (rest : GarblingSourceRest) (keys : OutputKeys)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource)
    (table : Pipeline.Table) (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (key : InputMacKey)
    (valid : OnCurve selected.1) (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after)
    (retainedCompatible : OracleTranscriptCompatible idealOracleHandler
      (sharedSourcePrefixReference referenceBefore rest) before) :
    sharedPipelinePhaseWeight adversary parameter auxiliary rest keys sample tag
      (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if sample ∈ sharedPipelineTagEvent rest keys table selected.1 key
      (sharedSourcePrefixReference referenceBefore rest) before after tag then 1 else 0) := by
  let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
  let view := fun input => selectedGateView
    (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
      (rowsForOutputKeys keys rest.algebraic.point.pointRandomness) input (retainedFullSource rest tag)) input
  have sourceEvent := sharedPipelineTagEvent_iff_source rest keys table selected.1 key
    referenceBefore before after tag labels valid bits mac retainedCompatible sample
  unfold sharedPipelinePhaseWeight
  dsimp only
  rw [sharedGateSourceGood_mass adversary parameter auxiliary (retainedFullTable rest keys tag) data view
    (fun input history => ¬ SharedPipelineTagGood rest keys (retainedFullTable rest keys tag) input sample.2
      (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) history) tag)
    (table, selected, before, labels, decision, after)]
  dsimp only
  rw [sharedGateSourcePhases_mass_factor_at adversary parameter auxiliary
    (retainedFullTable rest keys tag) table data view referenceBefore referenceAfter selected labels decision
    before after firstCompatible secondCompatible]
  rw [sourceEvent]
  by_cases sameTable : retainedFullTable rest keys tag = table
  · rw [sameTable]
    simp only [true_and]
    by_cases good : SharedPipelineTagGood rest keys table selected.1 sample.2
      (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) before) tag
    · simp only [data] at good
      simp only [data, view, sourceInputLabels, good, not_true_eq_false, if_false, true_and]
      rfl
    · simp only [data] at good
      simp only [data, good, not_false_eq_true, if_true, false_and, if_false, mul_zero]
  · have notGood : ¬ SharedPipelineTagGood rest keys table selected.1 sample.2
        (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) before) tag :=
      fun good => sameTable good.2.1
    simp only [data] at notGood
    simp only [data, sameTable, false_and, if_false, mul_zero, notGood]
    split <;> rfl

end
end Kriterion.ArgoMAC.Security
