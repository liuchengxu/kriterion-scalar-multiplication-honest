import Construction.SharedGarbling
import Proof.PackedAdapter
import Proof.Privacy.Simulator.SimulatorExecution
import Proof.Privacy.Simulator.SimulatorSampling

namespace Kriterion.ArgoMAC.Shared.Simulator
open BN254 Cryptography Security

abbrev OracleState := Security.SimulatorState FixedKeyIndex
abbrev State := CircuitSimulatorState FixedKeyIndex

/-- Both role names select the same public permutation and transcript. -/
def execute (state : OracleState) (command : FixedCommand) : OracleState :=
  tryProgramFixed state (fixedIndex command.1) command.2.1 command.2.2

/-- The interpreter retains the command order from the gate schedule. -/
def commands (state : OracleState) : List FixedCommand → OracleState
  | [] => state
  | command :: rest => commands (execute state command) rest

def program (state : OracleState) (schedule : List GateDirective) : OracleState :=
  commands state (scheduleCommands schedule)

/-- Each command checks the shared transcript before it changes a permutation. -/
theorem execute_invariant (state : OracleState) (command : FixedCommand)
    (valid : SimulatorInvariant state) : SimulatorInvariant (execute state command) :=
  tryProgramFixed_preservesInvariant state _ _ _ valid

/-- Every executed command preserves earlier transcript records. -/
theorem execute_records (state : OracleState) (command : FixedCommand) :
    state.fixedTranscript ⊆ (execute state command).fixedTranscript := by
  simp only [execute, tryProgramFixed]
  split <;> simp [programFixed, markBad]

/-- A collision flag persists through the remaining commands. -/
theorem commands_bad (state : OracleState) (values : List FixedCommand)
    (bad : state.bad = true) : (commands state values).bad = true := by
  induction values generalizing state with
  | nil => exact bad
  | cons command rest ih =>
      exact ih (execute state command) (tryProgramFixed_bad_of_bad state _ _ _ bad)

/-- Every command preserves the oracle invariant. -/
theorem commands_invariant (state : OracleState) (values : List FixedCommand)
    (valid : SimulatorInvariant state) : SimulatorInvariant (commands state values) := by
  induction values generalizing state with
  | nil => exact valid
  | cons command rest ih => exact ih _ (execute_invariant state command valid)

/-- The final transcript contains every earlier record. -/
theorem commands_records (state : OracleState) (values : List FixedCommand) :
    state.fixedTranscript ⊆ (commands state values).fixedTranscript := by
  induction values generalizing state with
  | nil => exact fun _ member => member
  | cons command rest ih =>
      intro record member
      exact ih _ (execute_records state command member)

/-- Fixed-key programming leaves the encryption oracle and hash oracle unchanged. -/
theorem commands_other (state : OracleState) (values : List FixedCommand) :
    (commands state values).encOracle = state.encOracle ∧
      (commands state values).hashOracle = state.hashOracle := by
  induction values generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons command rest ih =>
      have tail := ih (execute state command)
      by_cases checked : freshPermutationPairCheck state.fixedTranscript
        (fixedIndex command.1) command.2.1 command.2.2 = true
      all_goals simpa [commands, execute, tryProgramFixed, checked,
        programFixed, markBad] using tail

/-- Each successful command adds its shared-index record. -/
theorem execute_record (state : OracleState) (command : FixedCommand)
    (good : (execute state command).bad = false) :
    (PermutationRecord.mk .program .simulator (fixedIndex command.1) command.2.1 command.2.2) ∈
      (execute state command).fixedTranscript := by
  by_cases checked : freshPermutationPairCheck state.fixedTranscript
      (fixedIndex command.1) command.2.1 command.2.2 = true
  · simp [execute, tryProgramFixed, checked, programFixed]
  · simp [execute, tryProgramFixed, checked, markBad] at good

/-- A successful suffix has a successful initial state. -/
theorem commands_priorGood (state : OracleState) (values : List FixedCommand)
    (good : (commands state values).bad = false) : state.bad = false := by
  cases before : state.bad
  · rfl
  · have bad := commands_bad state values before
    rw [good] at bad
    contradiction

/-- A successful execution retains every command record. -/
theorem commands_record (state : OracleState) (values : List FixedCommand)
    (good : (commands state values).bad = false) (command : FixedCommand)
    (member : command ∈ values) :
    (PermutationRecord.mk .program .simulator (fixedIndex command.1) command.2.1 command.2.2) ∈
      (commands state values).fixedTranscript := by
  induction values generalizing state with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact commands_records (execute state command) rest
          (execute_record state command (commands_priorGood _ rest good))
      · exact ih (execute state first) good member

/-- Every successful command has its requested value in the final shared oracle. -/
theorem commands_apply (state : OracleState) (values : List FixedCommand)
    (valid : SimulatorInvariant state) (good : (commands state values).bad = false)
    (command : FixedCommand) (member : command ∈ values) :
    (commands state values).fixedOracle.permutation (fixedIndex command.1) command.2.1 = command.2.2 :=
  (commands_invariant state values valid).1 _ (commands_record state values good command member)

/-- A collision-free shared schedule makes each selected gate return its target. -/
theorem program_satisfies (state : OracleState) (schedule : List GateDirective)
    (valid : SimulatorInvariant state) (good : (program state schedule).bad = false)
    (directive : GateDirective) (member : directive ∈ schedule) :
    BitAdaptor.evaluate (Pipeline.fixedKeyGate (expandOracle (program state schedule).fixedOracle)
      directive.location directive.window) directive.table directive.bit directive.label = directive.target := by
  have assigned (record : PermutationRecord Pipeline.FixedKeyIndex Block)
      (recordMember : record ∈ directive.programRecords) :
      (program state schedule).fixedOracle.permutation (fixedIndex record.index)
        record.domain = record.range := by
    apply commands_apply state (scheduleCommands schedule) valid good
      (record.index, record.domain, record.range)
    apply List.mem_flatMap.mpr
    refine ⟨directive, member, ?_⟩
    apply List.mem_map.mpr
    exact ⟨record, List.mem_reverse.mpr recordMember, rfl⟩
  cases bit : directive.bit
  · apply hashGate_evaluate_of_matches (expandOracle (program state schedule).fixedOracle)
      directive.location directive.window directive.label directive.table directive.target
      (liftHashBlocks directive.lift.1)
    · rw [liftHashBlocks_value]
      exact directive.lift.2
    · intro slot
      have recordMember : fixedProgramRecord directive.location directive.window (.hash slot)
          directive.label (liftHashBlocks directive.lift.1 slot) ∈ directive.programRecords := by
        fin_cases slot <;> simp [GateDirective.programRecords, bit]
      exact assigned _ recordMember
  · apply padGate_evaluate_of_matches (expandOracle (program state schedule).fixedOracle)
      directive.location directive.window directive.label directive.table directive.target
      (targetPadBlocks directive.table directive.target)
    · exact targetPadBlocks_value directive.table directive.target
    · intro slot
      have recordMember : fixedProgramRecord directive.location directive.window (.pad slot)
          directive.label (targetPadBlocks directive.table directive.target slot) ∈ directive.programRecords := by
        fin_cases slot <;> simp [GateDirective.programRecords, bit]
      exact assigned _ recordMember

/-- A pad command cannot reuse a domain that a hash command records in the same slot. -/
theorem shared_domain_collision (state : OracleState) (kind : Pipeline.FixedKeyKind)
    (position : Fin coordinateBitCount) (slot : Fin 2) (domain hashRange padRange : Block) :
    (execute (execute state (⟨kind, position, .hash slot.castSucc⟩, domain, hashRange))
      (⟨kind, position, .pad slot⟩, domain, padRange)).bad = true := by
  by_contra notBad
  have good := Bool.eq_false_of_not_eq_true notBad
  let first := execute state (⟨kind, position, .hash slot.castSucc⟩, domain, hashRange)
  have firstGood : first.bad = false := tryProgramFixed_priorNotBad first _ _ _ good
  have prior := execute_record state (⟨kind, position, .hash slot.castSucc⟩, domain, hashRange) firstGood
  have fresh := (tryProgramFixed_badOrFresh first
    (fixedIndex ⟨kind, position, .pad slot⟩) domain padRange).resolve_left notBad
  exact (fresh _ prior rfl).1 rfl

/-- A pad command cannot reuse a range that a hash command records in the same slot. -/
theorem shared_range_collision (state : OracleState) (kind : Pipeline.FixedKeyKind)
    (position : Fin coordinateBitCount) (slot : Fin 2) (hashDomain padDomain range : Block) :
    (execute (execute state (⟨kind, position, .hash slot.castSucc⟩, hashDomain, range))
      (⟨kind, position, .pad slot⟩, padDomain, range)).bad = true := by
  by_contra notBad
  have good := Bool.eq_false_of_not_eq_true notBad
  let first := execute state (⟨kind, position, .hash slot.castSucc⟩, hashDomain, range)
  have firstGood : first.bad = false := tryProgramFixed_priorNotBad first _ _ _ good
  have prior := execute_record state (⟨kind, position, .hash slot.castSucc⟩, hashDomain, range) firstGood
  have fresh := (tryProgramFixed_badOrFresh first
    (fixedIndex ⟨kind, position, .pad slot⟩) padDomain range).resolve_left notBad
  exact (fresh _ prior rfl).2 rfl

/-- The offline state receives three public permutations per bucket. -/
def initialState (coin : SimulatorSampling.OfflineCoin)
    (oracles : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) : State := {
  oracle := {
    fixedOracle := oracles.1
    encOracle := oracles.2.1
    hashOracle := oracles.2.2
    fixedTranscript := []
    encTranscript := []
    hashTranscript := []
    commitments := []
    linking := none
    bad := false
  }
  curve := coin.1.curveRequest
  points := coin.1.pointRequests
  inputKey := coin.2.1
  bridgeKey := coin.2.2
}

/-- The offline sampler uses the existing private coin sampler and three-slot public oracles. -/
noncomputable def tape (_parameter : Nat) (_topology : Garbling.Topology) : PMF State :=
  letI : Nonempty (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :=
    ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩
  (PMF.uniformOfFintype (PublicOracle FixedKeyIndex EncPRF.PermutationIndex)).bind fun oracles =>
    SimulatorSampling.offline.law.map fun coin => initialState coin oracles

/-- The simulator programs only the selected gate schedule after it receives the output. -/
noncomputable def simulator [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.Simulator AffineInput (Option Point) Pipeline.Table Garbling.Labels
      Garbling.Topology State := {
  simulateGarble := fun parameter topology =>
    (tape parameter topology).map fun state => (state.table, state)
  simulateEncode := fun state input output => match output with
    | none =>
        let schedule := (state.selectedCurve input).schedule input (state.labels input).inputMac
        PMF.pure (state.labels input, {state with oracle := program state.oracle schedule})
    | some point =>
        (PMF.uniformOfFintype ((Fin 90 → Point) ×
          (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun sample =>
            let schedule := state.selectedSchedule input point (Vector.ofFn sample.1) sample.2
            (state.labels input, {state with oracle := program state.oracle schedule})
}

/-- The wire simulator sends exactly the selected Lamport blocks. -/
noncomputable def wireSimulator [FieldCertificate] [GroupCertificate] :=
  simulator.mapLabels (fun labels => Lamport.selectedLabels labels.inputMac)
    (fun _ : Nat => (⟨508, 91⟩ : Garbling.Topology))

/-- The wire simulator for the transmitted public value: it releases the packed
table the machine's ciphertext encodes. -/
noncomputable def packedWireSimulator [FieldCertificate] [GroupCertificate] :=
  wireSimulator.mapPublic Pipeline.Table.pack

end Kriterion.ArgoMAC.Shared.Simulator
