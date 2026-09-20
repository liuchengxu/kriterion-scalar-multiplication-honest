import Proof.Privacy.Simulator.Arithmetic.CheckedSlotCoupling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- The source bounds every base table, overlay, and fixed history. -/
def SharedSourceCounts (state : SharedOracleSource) (limit : Nat) : Prop :=
  (∀ index, (state.family.permutations index).base.used ≤ limit) ∧
  (∀ index, (state.family.permutations index).overlay.length ≤ limit) ∧
  (∀ index, (recordHistoryPairs state.metadata.fixedTranscript index).length ≤ limit)

/-- One recorded command adds at most one pair to each fixed history. -/
theorem recordHistoryPairs_program_length (metadata : Metadata) (command : SharedCommand) (index : Shared.FixedKeyIndex) :
    (recordHistoryPairs (metadata.program command).fixedTranscript index).length ≤
      (recordHistoryPairs metadata.fixedTranscript index).length + 1 := by
  change (recordHistoryPairs (PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2 :: metadata.fixedTranscript) index).length ≤ _
  rw [recordHistoryPairs_cons]
  split <;> simp

/-- An observed program adds at most one base entry and one overlay entry. -/
theorem checkedProgramFamilyValue_counts (family : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (memory : Memory) (next : SparseOracleFamily) (limit : Nat)
    (base : ∀ index, (family.permutations index).base.used ≤ limit)
    (overlay : ∀ index, (family.permutations index).overlay.length ≤ limit)
    (accepted : checkedProgramFamilyValue family oracle input target memory = some next) :
    (∀ index, (next.permutations index).base.used ≤ limit + 1) ∧
    (∀ index, (next.permutations index).overlay.length ≤ limit + 1) := by
  unfold checkedProgramFamilyValue at accepted
  cases observed : overlayQueryValue (family.permutations oracle).overlay.length memory with
  | none => simp only [observed, Option.map_none] at accepted; contradiction
  | some word =>
    simp only [observed, Option.map_some, Option.some.injEq] at accepted
    subst next
    have growth := programmedForwardNext_growth (family.permutations oracle) input (sparseWordValue (2 ^ 128) (by decide) word)
    constructor
    · intro index
      by_cases same : index = oracle
      · subst index
        simp only [SparseOracleFamily.updatePermutation, Function.update_self, programmedAfterForward]
        exact growth.1.trans (Nat.add_le_add_right (base oracle) 1)
      · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using (base index).trans (Nat.le_succ limit)
    · intro index
      by_cases same : index = oracle
      · subst index
        simp only [SparseOracleFamily.updatePermutation, Function.update_self, programmedAfterForward,
          growth.2, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        exact Nat.add_le_add_right (overlay oracle) 1
      · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using (overlay index).trans (Nat.le_succ limit)

/-- Every successful joint command increases the three count caps by at most one. -/
theorem checkedSlotJointSamples_counts (attempts limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (bounded : SharedSourceCounts state limit)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : (result, some next) ∈ (checkedSlotJointSamples attempts memory state command).support) :
    SharedSourceCounts next (limit + 1) := by
  unfold checkedSlotJointSamples at supported
  split at supported
  · obtain ⟨⟨before, spent⟩, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have outcome := congrArg Prod.snd equal
    dsimp only at outcome
    cases observed : checkedProgramFamilyValue state.family (sharedPhysicalIndex (.inl command.1))
        (blockFin command.2.1) (blockFin command.2.2) before with
    | none => simp only [observed, Option.map_none] at outcome; contradiction
    | some family =>
      simp only [observed, Option.map_some, Option.some.injEq] at outcome
      subst next
      have counts := checkedProgramFamilyValue_counts state.family _ _ _ before family limit bounded.1 bounded.2.1 observed
      refine ⟨counts.1, counts.2, ?_⟩
      intro index
      exact (recordHistoryPairs_program_length state.metadata command index).trans
        (Nat.add_le_add_right (bounded.2.2 index) 1)
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨rfl, rfl⟩ := supported
    exact ⟨fun index => (bounded.1 index).trans (Nat.le_succ limit),
      fun index => (bounded.2.1 index).trans (Nat.le_succ limit),
      fun index => (bounded.2.2 index).trans (Nat.le_succ limit)⟩

/-- The coupled command retains the exact count growth bound. -/
theorem checkedSlotCoupledSamples_counts (attempts limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (bounded : SharedSourceCounts state limit)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (checkedSlotCoupledSamples attempts memory state command).support) :
    SharedSourceCounts next (limit + 1) := by
  obtain ⟨⟨actual, source⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases source with
  | none => simp at equal
  | some found =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨rfl, rfl⟩ := equal
    exact checkedSlotJointSamples_counts attempts limit memory state command bounded actual found reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
