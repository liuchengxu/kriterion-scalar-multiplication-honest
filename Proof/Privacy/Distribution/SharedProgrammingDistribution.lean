import Proof.Privacy.Simulator.SharedSimulator
import Proof.Privacy.Source.AdaptivePermutationRatio

namespace Kriterion.ArgoMAC.Shared.Simulator
open BN254 Cryptography Security
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] transcriptOracleFintype

/-- Each command writes one canonical record to its actual shared slot. -/
def commandRecord (command : FixedCommand) : PermutationRecord FixedKeyIndex Block :=
  ⟨.program, .simulator, fixedIndex command.1, command.2.1, command.2.2⟩

def commandRecords (values : List FixedCommand) : List (PermutationRecord FixedKeyIndex Block) :=
  values.map commandRecord

/-- Fresh shared programming is exactly the finite transcript-extension operation. -/
theorem commands_state (state : OracleState) (values : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    (oracle : TranscriptOracle state.fixedTranscript) :
    commands {state with fixedOracle := oracle.1} values =
      {state with
        fixedOracle := (programTranscriptRecords state.fixedTranscript (commandRecords values) fresh oracle).1
        fixedTranscript := programRecordHistory state.fixedTranscript (commandRecords values)} := by
  induction values generalizing state with
  | nil => rfl
  | cons command remaining ih =>
      let record := commandRecord command
      have headFresh : FreshPermutationPair state.fixedTranscript record.index record.domain record.range := fresh.1
      have checked := (freshPermutationPairCheck_eq_true _ _ _ _).mpr headFresh
      have step : execute {state with fixedOracle := oracle.1} command =
          {state with
            fixedOracle := (programTranscriptOracle state.fixedTranscript record headFresh oracle).1
            fixedTranscript := record :: state.fixedTranscript} := by
        dsimp only [record, commandRecord] at checked
        simp only [execute, tryProgramFixed, checked, ite_true]
        rfl
      change commands (execute {state with fixedOracle := oracle.1} command) remaining = _
      rw [step]
      exact ih {state with fixedTranscript := record :: state.fixedTranscript} fresh.2
        (programTranscriptOracle state.fixedTranscript record headFresh oracle)

/-- The actual shared interpreter preserves the exact conditional-uniform oracle law. -/
theorem commands_uniform (state : OracleState) (values : List FixedCommand)
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    letI : Nonempty (TranscriptOracle (programRecordHistory state.fixedTranscript (commandRecords values))) :=
      ⟨programTranscriptRecords state.fixedTranscript (commandRecords values) fresh (Classical.arbitrary _)⟩
    (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => commands {state with fixedOracle := oracle.1} values) =
      (PMF.uniformOfFintype (TranscriptOracle
        (programRecordHistory state.fixedTranscript (commandRecords values)))).map
        (fun oracle => {state with
          fixedOracle := oracle.1
          fixedTranscript := programRecordHistory state.fixedTranscript (commandRecords values)}) := by
  letI : Nonempty (TranscriptOracle (programRecordHistory state.fixedTranscript (commandRecords values))) :=
    ⟨programTranscriptRecords state.fixedTranscript (commandRecords values) fresh (Classical.arbitrary _)⟩
  rw [← programTranscriptRecords_uniform state.fixedTranscript (commandRecords values) fresh, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map)
  funext oracle
  exact commands_state state values fresh oracle

/-- This factor is the exact mass of an external transcript in the actual three-slot oracle. -/
def transcriptMass [Fintype Block] (history : List (PermutationRecord FixedKeyIndex Block)) : ENNReal :=
  (PMF.uniformOfFintype (PermutationOracle FixedKeyIndex Block)).toOuterMeasure
    {oracle | PermutationTranscriptMatches oracle history}

/-- The exact query mass retains the entire shared programmed transcript. -/
theorem commands_queryMass_mul [Fintype Block] (state : OracleState) (values : List FixedCommand)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords values))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    transcriptMass (programRecordHistory state.fixedTranscript (commandRecords values)) *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries} =
      transcriptMass (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries) := by
  classical
  letI : Nonempty (TranscriptOracle (programRecordHistory state.fixedTranscript (commandRecords values))) :=
    ⟨programTranscriptRecords state.fixedTranscript (commandRecords values) fresh (Classical.arbitrary _)⟩
  rw [commands_uniform state values fresh, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  have result := @uniformSubtype_mass_mul
    (PermutationOracle FixedKeyIndex Block) inferInstance inferInstance
    (fun oracle => PermutationTranscriptMatches oracle
      (programRecordHistory state.fixedTranscript (commandRecords values)))
    (fun oracle => PermutationTranscriptMatches oracle queries)
    (inferInstanceAs (Fintype (TranscriptOracle
      (programRecordHistory state.fixedTranscript (commandRecords values)))))
    (inferInstanceAs (Nonempty (TranscriptOracle
      (programRecordHistory state.fixedTranscript (commandRecords values)))))
  have event : {oracle : PermutationOracle FixedKeyIndex Block |
      PermutationTranscriptMatches oracle (programRecordHistory state.fixedTranscript (commandRecords values)) ∧
        PermutationTranscriptMatches oracle queries} =
      {oracle | PermutationTranscriptMatches oracle
        (programRecordHistory state.fixedTranscript (commandRecords values) ++ queries)} := by
    ext oracle
    simp only [Set.mem_setOf_eq, PermutationTranscriptMatches, List.mem_append, or_imp, forall_and]
  rw [event] at result
  exact result


/-- The exact query law applies to the selected gate schedule of the actual shared simulator. -/
theorem program_queryMass_mul [Fintype Block] (state : OracleState) (schedule : List GateDirective)
    (queries : List (PermutationRecord FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (commandRecords (scheduleCommands schedule)))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    transcriptMass (programRecordHistory state.fixedTranscript (commandRecords (scheduleCommands schedule))) *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => program {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries} =
      transcriptMass (programRecordHistory state.fixedTranscript
        (commandRecords (scheduleCommands schedule)) ++ queries) :=
  commands_queryMass_mul state (scheduleCommands schedule) queries fresh

end
end Kriterion.ArgoMAC.Shared.Simulator
