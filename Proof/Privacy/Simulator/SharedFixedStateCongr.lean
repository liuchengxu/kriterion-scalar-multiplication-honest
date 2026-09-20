import Proof.Privacy.Transcript.SharedIdealTranscript
import Proof.Privacy.Distribution.SharedProgrammingDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Shared commands use only the fixed oracle and its recorded history. -/
theorem sharedCommands_fixed_fields (first second : Shared.Simulator.OracleState)
    (values : List FixedCommand) (fixed : first.fixedOracle = second.fixedOracle)
    (history : first.fixedTranscript = second.fixedTranscript) :
    (Shared.Simulator.commands first values).fixedOracle =
        (Shared.Simulator.commands second values).fixedOracle ∧
      (Shared.Simulator.commands first values).fixedTranscript =
        (Shared.Simulator.commands second values).fixedTranscript := by
  induction values generalizing first second with
  | nil => exact ⟨fixed, history⟩
  | cons value remaining ih =>
      apply ih
      · simp only [Shared.Simulator.execute, tryProgramFixed, history]
        split <;> simp only [programFixed, markBad, fixed]
      · simp only [Shared.Simulator.execute, tryProgramFixed, history]
        split <;> simp only [programFixed, markBad, history]

/-- The shared recording handler also uses only the fixed fields for its fixed history. -/
theorem sharedIdealTranscriptFinal_fixed_fields (first second : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : first.fixedOracle = second.fixedOracle)
    (history : first.fixedTranscript = second.fixedTranscript) :
    (transcriptFinalState idealOracleHandler first transcript).fixedOracle =
        (transcriptFinalState idealOracleHandler second transcript).fixedOracle ∧
      (transcriptFinalState idealOracleHandler first transcript).fixedTranscript =
        (transcriptFinalState idealOracleHandler second transcript).fixedTranscript := by
  induction transcript generalizing first second with
  | nil => exact ⟨fixed, history⟩
  | cons entry remaining ih =>
      apply ih
      · rcases entry with ⟨request, answer⟩
        cases request <;> exact fixed
      · rcases entry with ⟨request, answer⟩
        cases request <;>
          simp only [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash, fixed, history]

attribute [local instance] transcriptOracleFintype

/-- Equal recorded histories give equal conditional programmed fixed-query probabilities. -/
theorem sharedCommands_conditional_mass_congr [Fintype Block]
    (first second : Shared.Simulator.OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (history : first.fixedTranscript = second.fixedTranscript)
    [Nonempty (TranscriptOracle first.fixedTranscript)]
    [Nonempty (TranscriptOracle second.fixedTranscript)] :
    ((PMF.uniformOfFintype (TranscriptOracle first.fixedTranscript)).map
      (fun oracle => Shared.Simulator.commands {first with fixedOracle := oracle.1} values)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries} =
    ((PMF.uniformOfFintype (TranscriptOracle second.fixedTranscript)).map
      (fun oracle => Shared.Simulator.commands {second with fixedOracle := oracle.1} values)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries} := by
  rcases first with ⟨fixed1, enc1, hash1, history1, encHistory1, hashHistory1, commitments1, linking1, bad1⟩
  rcases second with ⟨fixed2, enc2, hash2, history2, encHistory2, hashHistory2, commitments2, linking2, bad2⟩
  dsimp only at history
  subst history2
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle history1)).toOuterMeasure
  ext oracle
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  apply Iff.of_eq
  apply congrArg (fun fixed => PermutationTranscriptMatches fixed queries)
  exact (sharedCommands_fixed_fields
    ⟨oracle.1, enc1, hash1, history1, encHistory1, hashHistory1, commitments1, linking1, bad1⟩
    ⟨oracle.1, enc2, hash2, history1, encHistory2, hashHistory2, commitments2, linking2, bad2⟩
    values rfl rfl).1

end
end Kriterion.ArgoMAC.Security
