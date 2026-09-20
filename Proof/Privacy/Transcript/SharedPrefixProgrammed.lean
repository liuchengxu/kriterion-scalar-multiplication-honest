import Proof.Privacy.Transcript.SharedIdealTranscript
import Proof.Privacy.Distribution.SharedProgrammingDistribution
import Proof.Privacy.Source.Valid.ValidSourceKernel

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] transcriptOracleFintype

/-- The exact shared prefix mass gives its conditional uniform oracle law. -/
theorem sharedFixedTranscript_event_mass [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (event : PermutationOracle Shared.FixedKeyIndex Block → Prop)
    [Nonempty (TranscriptOracle history)] :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | PermutationTranscriptMatches oracle history ∧ event oracle} =
      Shared.Simulator.transcriptMass history *
        (PMF.uniformOfFintype (TranscriptOracle history)).toOuterMeasure {oracle | event oracle.1} := by
  exact (@uniformSubtype_mass_mul (PermutationOracle Shared.FixedKeyIndex Block)
    inferInstance inferInstance (PermutationTranscriptMatches · history) event
    (transcriptOracleFintype history) (show Nonempty (TranscriptOracle history) from inferInstance)).symm

/-- The actual shared prefix gives the exact conditional programmed-oracle experiment. -/
theorem sharedIdealPrefixProgrammed_mass [Fintype Block]
    (state : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (values : List FixedCommand)
    (empty : state.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler state before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)] :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (Shared.Simulator.commands
            (transcriptFinalState idealOracleHandler {state with fixedOracle := oracle} before) values) after} =
      Shared.Simulator.transcriptMass (transcriptFinalState idealOracleHandler state before).fixedTranscript *
        ((PMF.uniformOfFintype
          (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)).map
            (fun oracle => Shared.Simulator.commands
              {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle.1} values)).toOuterMeasure
                {programmed | OracleTranscriptCompatible idealOracleHandler programmed after} := by
  have history := sharedIdealTranscriptFinal_fixedHistory state before compatible
  rw [empty, List.append_nil] at history
  have matching (oracle : PermutationOracle Shared.FixedKeyIndex Block) :
      PermutationTranscriptMatches oracle
        (transcriptFinalState idealOracleHandler state before).fixedTranscript ↔
      PermutationTranscriptMatches oracle (sharedFixedTranscriptRecords before) := by
    rw [history]
    simp only [PermutationTranscriptMatches, List.mem_reverse]
  rw [PMF.toOuterMeasure_map_apply]
  simp only [Set.preimage_setOf_eq]
  rw [← sharedFixedTranscript_event_mass _
    (fun oracle => OracleTranscriptCompatible idealOracleHandler
      (Shared.Simulator.commands
        {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle} values) after)]
  apply congrArg (PMF.toOuterMeasure (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)))
  ext oracle
  simp only [Set.mem_setOf_eq]
  rw [matching, ← sharedIdealPrefixCompatible_iff_matches state before compatible oracle]
  apply and_congr_right
  intro valid
  rw [sharedIdealTranscriptFinal_updateFixed state oracle before compatible valid]

/-- Nonfixed-compatible suffix answers leave only the fixed query equations. -/
theorem sharedIdealCompatible_iff_fixed_of_nonfixed (state : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (nonfixed : SharedNonFixedTranscriptCompatible
      (state.fixedOracle, state.encOracle, state.hashOracle) transcript) :
    OracleTranscriptCompatible idealOracleHandler state transcript ↔
      PermutationTranscriptMatches state.fixedOracle (sharedFixedTranscriptRecords transcript) := by
  rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff]
  exact and_iff_left nonfixed

/-- The shared prefix and programmed suffix have the exact fixed-query conditional mass. -/
theorem sharedIdealPrefixProgrammed_fixed_mass [Fintype Block]
    (state : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (values : List FixedCommand)
    (empty : state.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler state before)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (state.fixedOracle, state.encOracle, state.hashOracle) after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)] :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (Shared.Simulator.commands
            (transcriptFinalState idealOracleHandler {state with fixedOracle := oracle} before) values) after} =
      Shared.Simulator.transcriptMass (transcriptFinalState idealOracleHandler state before).fixedTranscript *
        ((PMF.uniformOfFintype
          (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)).map
            (fun oracle => Shared.Simulator.commands
              {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle.1} values)).toOuterMeasure
                {programmed | PermutationTranscriptMatches programmed.fixedOracle (sharedFixedTranscriptRecords after)} := by
  rw [sharedIdealPrefixProgrammed_mass state before after values empty compatible]
  apply congrArg (_ * ·)
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply congrArg (PMF.uniformOfFintype
    (TranscriptOracle (transcriptFinalState idealOracleHandler state before).fixedTranscript)).toOuterMeasure
  ext oracle
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  apply sharedIdealCompatible_iff_fixed_of_nonfixed
  have same := Shared.Simulator.commands_other
    {transcriptFinalState idealOracleHandler state before with fixedOracle := oracle.1} values
  rw [same.1, same.2, (sharedIdealTranscriptFinal_oracles state before).2.1,
    (sharedIdealTranscriptFinal_oracles state before).2.2]
  exact (sharedNonFixedTranscriptCompatible_fixed _ state.fixedOracle _ _ after).mpr nonfixed

end
end Kriterion.ArgoMAC.Security
