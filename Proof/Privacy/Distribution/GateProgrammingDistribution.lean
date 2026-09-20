/- This file proves the exact oracle law for fresh gate programming. -/

import Cryptography.Permutation
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- This fiber contains every oracle that gives the recorded answers. -/
def TranscriptOracle {Index : Type} (history : List (PermutationRecord Index Block)) :=
  {oracle : PermutationOracle Index Block // PermutationTranscriptMatches oracle history}

/-- This fiber contains every output that the transcript does not use in one bucket. -/
def UnusedTranscriptOutput {Index : Type}
    (history : List (PermutationRecord Index Block)) (index : Index) :=
  {output : Block // ∀ record ∈ history, record.index = index → record.range ≠ output}

local instance transcriptOracleFintype {Index : Type} [Fintype Index]
    (history : List (PermutationRecord Index Block)) : Fintype (TranscriptOracle history) := by
  classical
  unfold TranscriptOracle
  infer_instance

local instance unusedTranscriptOutputFintype {Index : Type}
    (history : List (PermutationRecord Index Block)) (index : Index) :
    Fintype (UnusedTranscriptOutput history index) := by
  classical
  unfold UnusedTranscriptOutput
  letI : DecidablePred (fun output : Block => ∀ record ∈ history, record.index = index → record.range ≠ output) := fun _ => Classical.propDecidable _
  infer_instance

/-- This operation extends a compatible oracle by one fresh record. -/
def programTranscriptOracle {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (record : PermutationRecord Index Block)
    (fresh : FreshPermutationPair history record.index record.domain record.range)
    (oracle : TranscriptOracle history) : TranscriptOracle (record :: history) := by
  refine ⟨programPermutation oracle.1 record.index record.domain record.range, ?_⟩
  intro prior member
  rcases List.mem_cons.mp member with same | member
  · subst prior
    exact programPermutation_apply _ _ _ _
  · exact programPermutation_preserves oracle.1 record.index record.domain record.range
      prior (oracle.2 prior member) (fresh prior member)

/-- The exact family extension loses only the old output of the programmed input. -/
def programTranscriptOracleEquiv {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (record : PermutationRecord Index Block)
    (fresh : FreshPermutationPair history record.index record.domain record.range) :
    TranscriptOracle history ≃
      TranscriptOracle (record :: history) × UnusedTranscriptOutput history record.index where
  toFun oracle :=
    (programTranscriptOracle history record fresh oracle,
      ⟨oracle.1.permutation record.index record.domain, by
        intro prior member sameIndex equal
        apply (fresh prior member sameIndex).1
        apply (oracle.1.permutation prior.index).injective
        rw [oracle.2 prior member]
        simpa only [sameIndex] using equal⟩)
  invFun pair :=
    ⟨programPermutation pair.1.1 record.index record.domain pair.2.1, by
      intro prior member
      exact programPermutation_preserves pair.1.1 record.index record.domain pair.2.1
        prior (pair.1.2 prior (List.mem_cons_of_mem _ member))
          (fun same => ⟨(fresh prior member same).1, pair.2.2 prior member same⟩)⟩
  left_inv oracle := by
    apply Subtype.ext
    exact congrArg Prod.fst (swapProgramPair_involutive record.index record.domain
      (oracle.1, record.range))
  right_inv pair := by
    have assigned : pair.1.1.permutation record.index record.domain = record.range :=
      pair.1.2 record (List.mem_cons_self ..)
    have restore := swapProgramPair_involutive record.index record.domain (pair.1.1, pair.2.1)
    apply Prod.ext
    · apply Subtype.ext
      have oracle := congrArg Prod.fst restore
      simpa only [swapProgramPair, programTranscriptOracle, assigned] using oracle
    · apply Subtype.ext
      exact programPermutation_apply _ _ _ _

/-- The exact eager swap gives the uniform oracle fiber for the extended transcript. -/
theorem programTranscriptOracle_uniform {Index : Type} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (record : PermutationRecord Index Block)
    (fresh : FreshPermutationPair history record.index record.domain record.range)
    [Nonempty (TranscriptOracle history)] :
    letI : Nonempty (TranscriptOracle (record :: history)) :=
      ⟨programTranscriptOracle history record fresh (Classical.arbitrary _)⟩
    (PMF.uniformOfFintype (TranscriptOracle history)).map
      (programTranscriptOracle history record fresh) =
      PMF.uniformOfFintype (TranscriptOracle (record :: history)) := by
  letI : Nonempty (TranscriptOracle (record :: history)) :=
    ⟨programTranscriptOracle history record fresh (Classical.arbitrary _)⟩
  letI : Nonempty (UnusedTranscriptOutput history record.index) :=
    ⟨⟨record.range, fun prior member same => (fresh prior member same).2⟩⟩
  let split := programTranscriptOracleEquiv history record fresh
  change (PMF.uniformOfFintype (TranscriptOracle history)).map (Prod.fst ∘ split) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween split, map_uniform_prod_fst]

/-- The family operation uses the exact compatible-permutation update in its active bucket. -/
theorem programTranscriptOracle_activeBucket {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (record : PermutationRecord Index Block)
    (fresh : FreshPermutationPair history record.index record.domain record.range)
    (oracle : TranscriptOracle history)
    (domain range : Set Block) [DecidablePred (· ∈ domain)] [DecidablePred (· ∈ range)]
    (assignment : domain ≃ range) (freshDomain : record.domain ∉ domain)
    (freshRange : record.range ∉ range)
    (matching : ∀ value : domain, oracle.1.permutation record.index value = assignment value) :
    (programTranscriptOracle history record fresh oracle).1.permutation record.index =
      (programCompatiblePermutation domain range assignment record.domain freshDomain
        record.range freshRange ⟨oracle.1.permutation record.index, matching⟩).1 := by
  simp [programTranscriptOracle, programPermutation, programCompatiblePermutation]

/-- This list condition permits shared buckets and requires fresh assignments in execution order. -/
def FreshRecordSchedule {Index : Type}
    (history : List (PermutationRecord Index Block)) : List (PermutationRecord Index Block) → Prop
  | [] => True
  | record :: remaining =>
      FreshPermutationPair history record.index record.domain record.range ∧
        FreshRecordSchedule (record :: history) remaining

/-- This function records the assignments in the simulator's transcript order. -/
def programRecordHistory {Index : Type} (history records : List (PermutationRecord Index Block)) :
    List (PermutationRecord Index Block) := records.foldl (fun current record => record :: current) history

/-- This function applies each exact transcript extension in execution order. -/
def programTranscriptRecords {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (records : List (PermutationRecord Index Block))
    (fresh : FreshRecordSchedule history records) (oracle : TranscriptOracle history) :
    TranscriptOracle (programRecordHistory history records) :=
  match records with
  | [] => oracle
  | record :: remaining => programTranscriptRecords (record :: history) remaining fresh.2
      (programTranscriptOracle history record fresh.1 oracle)

/-- Every fresh assignment sequence gives the exact uniform extended oracle family. -/
theorem programTranscriptRecords_uniform {Index : Type} [Fintype Index] [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (records : List (PermutationRecord Index Block))
    (fresh : FreshRecordSchedule history records) [Nonempty (TranscriptOracle history)] :
    letI : Nonempty (TranscriptOracle (programRecordHistory history records)) :=
      ⟨programTranscriptRecords history records fresh (Classical.arbitrary _)⟩
    (PMF.uniformOfFintype (TranscriptOracle history)).map
      (programTranscriptRecords history records fresh) =
      PMF.uniformOfFintype (TranscriptOracle (programRecordHistory history records)) := by
  induction records generalizing history with
  | nil => exact PMF.map_id _
  | cons record remaining inductionHypothesis =>
      letI : Nonempty (TranscriptOracle (record :: history)) :=
        ⟨programTranscriptOracle history record fresh.1 (Classical.arbitrary _)⟩
      change (PMF.uniformOfFintype (TranscriptOracle history)).map
        ((programTranscriptRecords (record :: history) remaining fresh.2) ∘
          programTranscriptOracle history record fresh.1) = _
      rw [← PMF.map_comp, programTranscriptOracle_uniform]
      exact inductionHypothesis (record :: history) fresh.2

/-- This function runs the concrete checked programming operation on each assignment. -/
def programRecordSchedule (state : SimulatorState)
    (records : List (PermutationRecord Pipeline.FixedKeyIndex Block)) : SimulatorState :=
  records.foldl (fun current record =>
    tryProgramFixed current record.index record.domain record.range) state

private theorem tryProgramFixed_fresh (state : SimulatorState)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block)
    (fresh : FreshPermutationPair state.fixedTranscript record.index record.domain record.range) :
    tryProgramFixed state record.index record.domain record.range =
      programFixed state record.index record.domain record.range := by
  rw [tryProgramFixed, (freshPermutationPairCheck_eq_true _ _ _ _).mpr fresh]
  rfl

/-- The concrete operation keeps the exact conditional-uniform oracle family. -/
theorem programFixedSlot_uniform (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (slot : Pipeline.FixedKeySlot)
    (label block : Block)
    (fresh : FreshPermutationPair state.fixedTranscript (fixedKeyIndex location window slot)
      (gateInput location label) (block ^^^ (gateInput location label)))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let record := fixedProgramRecord location window slot label block
    letI : Nonempty (TranscriptOracle (record :: state.fixedTranscript)) :=
      ⟨programTranscriptOracle state.fixedTranscript record fresh (Classical.arbitrary _)⟩
    (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
      programFixedSlot {state with fixedOracle := oracle.1} location window slot label block) =
      (PMF.uniformOfFintype (TranscriptOracle (record :: state.fixedTranscript))).map
        (fun oracle => {state with
          fixedOracle := oracle.1
          fixedTranscript := record :: state.fixedTranscript}) := by
  dsimp only
  let record := fixedProgramRecord location window slot label block
  letI : Nonempty (TranscriptOracle (record :: state.fixedTranscript)) :=
    ⟨programTranscriptOracle state.fixedTranscript record fresh (Classical.arbitrary _)⟩
  rw [← programTranscriptOracle_uniform state.fixedTranscript record fresh, PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map)
  funext oracle
  unfold programFixedSlot
  have checked := (freshPermutationPairCheck_eq_true _ _ _ _).mpr fresh
  simp only [tryProgramFixed, checked, ite_true]
  rfl

/-- Pairwise fresh assignments stay fresh after all earlier assignments. -/
theorem freshRecordSchedule_of_pairwise {Index : Type}
    (history records : List (PermutationRecord Index Block))
    (againstHistory : ∀ record ∈ records,
      FreshPermutationPair history record.index record.domain record.range)
    (pairwise : records.Pairwise fun first second => first.index = second.index →
      first.domain ≠ second.domain ∧ first.range ≠ second.range) :
    FreshRecordSchedule history records := by
  induction records generalizing history with
  | nil => trivial
  | cons record remaining inductionHypothesis =>
      refine ⟨againstHistory record (List.mem_cons_self ..), ?_⟩
      apply inductionHypothesis
      · intro current member prior priorMember sameIndex
        rcases List.mem_cons.mp priorMember with same | earlier
        · subst prior
          exact (List.pairwise_cons.mp pairwise).1 current member sameIndex
        · exact againstHistory current (List.mem_cons_of_mem _ member) prior earlier sameIndex
      · exact (List.pairwise_cons.mp pairwise).2

private theorem programRecordSchedule_append (state : SimulatorState)
    (first second : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    programRecordSchedule state (first ++ second) =
      programRecordSchedule (programRecordSchedule state first) second := by
  exact List.foldl_append

/-- This function lists the actual gate assignments in execution order. -/
def gateProgramRecords (schedule : List GateDirective) :
    List (PermutationRecord Pipeline.FixedKeyIndex Block) :=
  schedule.flatMap fun directive => directive.programRecords.reverse

private theorem gateDirective_eq_recordSchedule (directive : GateDirective) (state : SimulatorState) :
    directive.apply state = programRecordSchedule state directive.programRecords.reverse := by
  cases branch : directive.bit <;>
    simp [GateDirective.apply, GateDirective.programRecords, programRecordSchedule,
      programGateForTarget, programGate, branch, programHashGate, programPadGate,
      programFixedSlot, fixedProgramRecord]

/-- This identity uses the exact execution order of the concrete gate schedule. -/
theorem programGateSchedule_eq_recordSchedule (state : SimulatorState) (schedule : List GateDirective) :
    programGateSchedule state schedule = programRecordSchedule state (gateProgramRecords schedule) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons directive remaining inductionHypothesis =>
      change programGateSchedule (directive.apply state) remaining =
        programRecordSchedule state (directive.programRecords.reverse ++ gateProgramRecords remaining)
      rw [programRecordSchedule_append, ← gateDirective_eq_recordSchedule, inductionHypothesis]

private theorem gateProgramRecords_metadata (schedule : List GateDirective) :
    ∀ record ∈ gateProgramRecords schedule, record.action = .program ∧ record.origin = .simulator := by
  intro record member
  obtain ⟨directive, _, member⟩ := List.mem_flatMap.mp member
  have member := List.mem_reverse.mp member
  cases branch : directive.bit <;>
    simp only [GateDirective.programRecords, branch, Bool.false_eq_true, if_false, if_true,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Fresh checked programs retain all state fields except the oracle and its extended transcript. -/
theorem programRecordSchedule_state (state : SimulatorState)
    (records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript records)
    (metadata : ∀ record ∈ records, record.action = .program ∧ record.origin = .simulator)
    (oracle : TranscriptOracle state.fixedTranscript) :
    programRecordSchedule {state with fixedOracle := oracle.1} records =
      {state with
        fixedOracle := (programTranscriptRecords state.fixedTranscript records fresh oracle).1
        fixedTranscript := programRecordHistory state.fixedTranscript records} := by
  induction records generalizing state with
  | nil => rfl
  | cons record remaining inductionHypothesis =>
      have fields := metadata record (List.mem_cons_self ..)
      have canonical : PermutationRecord.mk .program .simulator record.index record.domain record.range =
          record := by cases record; simp_all
      change programRecordSchedule
        (tryProgramFixed {state with fixedOracle := oracle.1} record.index record.domain record.range)
          remaining = _
      rw [tryProgramFixed_fresh {state with fixedOracle := oracle.1} record fresh.1]
      have step : programFixed {state with fixedOracle := oracle.1}
          record.index record.domain record.range =
          {state with
            fixedOracle := (programTranscriptOracle state.fixedTranscript record fresh.1 oracle).1
            fixedTranscript := record :: state.fixedTranscript} := by
        unfold programFixed
        rw [canonical]
        rfl
      rw [step]
      exact inductionHypothesis {state with fixedTranscript := record :: state.fixedTranscript}
        fresh.2 (fun current member => metadata current (List.mem_cons_of_mem _ member))
        (programTranscriptOracle state.fixedTranscript record fresh.1 oracle)

/-- Fresh programming does not set the bad flag. -/
theorem programRecordSchedule_bad_eq (state : SimulatorState)
    (records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript records)
    (metadata : ∀ record ∈ records, record.action = .program ∧ record.origin = .simulator) :
    (programRecordSchedule state records).bad = state.bad := by
  induction records generalizing state with
  | nil => rfl
  | cons record remaining inductionHypothesis =>
      have fields := metadata record (List.mem_cons_self ..)
      have canonical : PermutationRecord.mk .program .simulator record.index record.domain record.range =
          record := by cases record; simp_all
      change (programRecordSchedule
        (tryProgramFixed state record.index record.domain record.range) remaining).bad = state.bad
      rw [tryProgramFixed_fresh state record fresh.1]
      have freshTail : FreshRecordSchedule
          (programFixed state record.index record.domain record.range).fixedTranscript remaining := by
        simpa only [programFixed, canonical] using fresh.2
      exact inductionHypothesis (programFixed state record.index record.domain record.range)
        freshTail (fun current member => metadata current (List.mem_cons_of_mem _ member))

/-- Fresh selected assignments preserve the actual gate schedule's bad flag. -/
theorem programGateSchedule_bad_eq_of_freshRecords (state : SimulatorState)
    (schedule : List GateDirective)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule)) :
    (programGateSchedule state schedule).bad = state.bad := by
  rw [programGateSchedule_eq_recordSchedule]
  exact programRecordSchedule_bad_eq state _ fresh (gateProgramRecords_metadata schedule)

/-- Pairwise fresh selected assignments cannot cause a programming collision. -/
theorem programGateSchedule_bad_eq_of_pairwise (state : SimulatorState)
    (schedule : List GateDirective)
    (againstHistory : ∀ record ∈ gateProgramRecords schedule,
      FreshPermutationPair state.fixedTranscript record.index record.domain record.range)
    (pairwise : (gateProgramRecords schedule).Pairwise fun first second => first.index = second.index →
      first.domain ≠ second.domain ∧ first.range ≠ second.range) :
    (programGateSchedule state schedule).bad = state.bad :=
  programGateSchedule_bad_eq_of_freshRecords state schedule
    (freshRecordSchedule_of_pairwise _ _ againstHistory pairwise)

/-- The actual gate schedule gives the uniform oracle family for every retained assignment. -/
theorem programGateSchedule_uniform (state : SimulatorState) (schedule : List GateDirective)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let history := programRecordHistory state.fixedTranscript (gateProgramRecords schedule)
    letI : Nonempty (TranscriptOracle history) :=
      ⟨programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh
        (Classical.arbitrary _)⟩
    (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
      programGateSchedule {state with fixedOracle := oracle.1} schedule) =
      (PMF.uniformOfFintype (TranscriptOracle history)).map (fun oracle =>
        {state with
          fixedOracle := oracle.1
          fixedTranscript := history}) := by
  dsimp only
  letI : Nonempty (TranscriptOracle (programRecordHistory state.fixedTranscript (gateProgramRecords schedule))) :=
    ⟨programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh
      (Classical.arbitrary _)⟩
  rw [← programTranscriptRecords_uniform state.fixedTranscript (gateProgramRecords schedule) fresh,
    PMF.map_comp]
  apply congrArg ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map)
  funext oracle
  rw [programGateSchedule_eq_recordSchedule]
  exact programRecordSchedule_state state _ fresh (gateProgramRecords_metadata schedule) oracle

private theorem mem_programRecordHistory {Index : Type}
    (history records : List (PermutationRecord Index Block))
    (record : PermutationRecord Index Block) (member : record ∈ history) :
    record ∈ programRecordHistory history records := by
  induction records generalizing history with
  | nil => exact member
  | cons current remaining inductionHypothesis =>
      exact inductionHypothesis (current :: history) (List.mem_cons_of_mem _ member)

/-- The extended family gives every prior forward and inverse query its recorded answer. -/
theorem programTranscriptRecords_priorAnswers {Index : Type} [DecidableEq Index]
    (history records : List (PermutationRecord Index Block))
    (fresh : FreshRecordSchedule history records) (oracle : TranscriptOracle history)
    (record : PermutationRecord Index Block) (member : record ∈ history) :
    let updated := (programTranscriptRecords history records fresh oracle).1
    updated.permutation record.index record.domain = record.range ∧
      (updated.permutation record.index).symm record.range = record.domain := by
  have answer := (programTranscriptRecords history records fresh oracle).2 record
    (mem_programRecordHistory history records record member)
  refine ⟨answer, ?_⟩
  rw [← answer, Equiv.symm_apply_apply]

/-- The concrete gate schedule preserves every recorded forward and inverse answer. -/
theorem programGateSchedule_priorAnswers (state : SimulatorState) (schedule : List GateDirective)
    (matching : PermutationTranscriptMatches state.fixedOracle state.fixedTranscript)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    (record : PermutationRecord Pipeline.FixedKeyIndex Block)
    (member : record ∈ state.fixedTranscript) :
    let updated := (programGateSchedule state schedule).fixedOracle
    updated.permutation record.index record.domain = record.range ∧
      (updated.permutation record.index).symm record.range = record.domain := by
  let oracle : TranscriptOracle state.fixedTranscript := ⟨state.fixedOracle, matching⟩
  have stateLaw := programRecordSchedule_state state (gateProgramRecords schedule) fresh
    (gateProgramRecords_metadata schedule) oracle
  have oracleLaw : (programGateSchedule state schedule).fixedOracle =
      (programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh oracle).1 := by
    rw [programGateSchedule_eq_recordSchedule]
    exact congrArg SimulatorState.fixedOracle stateLaw
  dsimp only
  rw [oracleLaw]
  exact programTranscriptRecords_priorAnswers _ _ fresh oracle record member

end
end Kriterion.ArgoMAC.Security
