import Proof.Privacy.Transcript.SharedIdealGateGame
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The concrete source choice and continuation form the exact two-phase experiment. -/
theorem sharedGateSourcePhases_eq {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView) :
    ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data) =
    (twoPhaseTranscript idealOracleHandler (adversary.chooseInput parameter table auxiliary)
      (fun state selected => PMF.pure
        (sourceInputLabels data selected.1,
          sharedProgramSelectedGateView state selected.1 (sourceInputLabels data selected.1).inputMac (view selected.1)))
      (fun selected labels => adversary.decide parameter table labels auxiliary selected.2)
      (sharedInitialSourceOracle data)).map (Prod.mk table) := by
  simp only [sharedGateSourceChoose, sharedGateSourceObserve, twoPhaseTranscript, PMF.bind_map,
    PMF.map_bind, PMF.pure_bind, PMF.map_comp, Function.comp_def]

private theorem tagged_mass {A B : Type*} (distribution : PMF B) (tag : A) (value : B) :
    (distribution.map (Prod.mk tag)) (tag, value) = distribution value := by
  simp only [PMF.map_apply, Prod.mk.injEq, true_and]
  rw [tsum_eq_single value]
  · simp
  · intro other different
    simp [Ne.symm different]

/-- The endpoint mass separates both adversary factors from the exact source event. -/
theorem sharedGateSourcePhases_mass_factor {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun choice =>
      sharedGateSourceObserve adversary parameter auxiliary table choice (view choice.1) data)
        (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) before ∧
      sourceInputLabels data selected.1 = labels ∧
      OracleTranscriptCompatible idealOracleHandler
        (sharedProgramSelectedGateView (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) before)
          selected.1 (sourceInputLabels data selected.1).inputMac (view selected.1)) after then 1 else 0) := by
  rw [sharedGateSourcePhases_eq, tagged_mass, twoPhaseTranscript_mass_factor
    idealOracleHandler (adversary.chooseInput parameter table auxiliary)
    (fun state selected => PMF.pure
      (sourceInputLabels data selected.1,
        sharedProgramSelectedGateView state selected.1 (sourceInputLabels data selected.1).inputMac (view selected.1)))
    (fun selected labels => adversary.decide parameter table labels auxiliary selected.2)
    (sharedInitialSourceOracle data) referenceBefore referenceAfter selected labels decision before after
    firstCompatible secondCompatible]
  simp only [twoPhaseSourceMass, PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
  by_cases compatible : OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) before
  · simp only [compatible, true_and, if_true]
  · simp only [compatible, false_and, if_false]

/-- The table guard lets both adversary factors use the observed table. -/
theorem sharedGateSourcePhases_mass_factor_at {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table observedTable : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (referenceBefore referenceAfter : Shared.Simulator.OracleState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun choice =>
      sharedGateSourceObserve adversary parameter auxiliary table choice (view choice.1) data)
        (observedTable, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter observedTable auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter observedTable labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if table = observedTable ∧
      OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) before ∧
      sourceInputLabels data selected.1 = labels ∧
      OracleTranscriptCompatible idealOracleHandler
        (sharedProgramSelectedGateView (transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) before)
          selected.1 (sourceInputLabels data selected.1).inputMac (view selected.1)) after then 1 else 0) := by
  by_cases same : table = observedTable
  · subst observedTable
    simp only [true_and]
    exact sharedGateSourcePhases_mass_factor adversary parameter auxiliary table data view
      referenceBefore referenceAfter selected labels decision before after firstCompatible secondCompatible
  · simp only [same, false_and, if_false, mul_zero]
    rw [sharedGateSourcePhases_eq, PMF.map_apply]
    simp only [Prod.mk.injEq, Ne.symm same, false_and, if_false, tsum_zero]

end
end Kriterion.ArgoMAC.Security
