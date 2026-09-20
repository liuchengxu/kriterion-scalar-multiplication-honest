import Proof.Privacy.Simulator.Arithmetic.SharedCommandListProgram
import Proof.Privacy.Simulator.Arithmetic.SharedPublicGrowth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- A larger limit retains every finite source count. -/
theorem SharedSourceCounts.mono {state : SharedOracleSource} {first second : Nat}
    (bounded : SharedSourceCounts state first) (increase : first ≤ second) :
    SharedSourceCounts state second :=
  ⟨fun index => (bounded.1 index).trans increase,
    fun index => (bounded.2.1 index).trans increase,
    fun index => (bounded.2.2 index).trans increase⟩

/-- An accepted cutoff result also occurs in the exact source distribution. -/
theorem drawCutoffLaw_supported {A : Type} (attempts : Nat) (draw : Draw A) (value : A)
    (member : some value ∈ (drawCutoffLaw attempts draw).support) : value ∈ draw.distribution.support := by
  rw [PMF.mem_support_iff] at member ⊢
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr member) (drawCutoffLaw_upper attempts draw value))

/-- Each source command adds at most one entry to each table and leaves the hash table unchanged. -/
theorem sharedSourceCommand_growth (attempts limit : Nat) (state next : SharedOracleSource)
    (command : SharedCommand) (bounded : SharedSourceCounts state limit)
    (member : some ((), next) ∈ (sharedSourceCutoff attempts (.inl (.program command)) state).support) :
    SharedSourceCounts next (limit + 1) ∧ next.family.hash = state.family.hash := by
  change some ((), next) ∈ (drawCutoffLaw attempts (sharedInternalSourceDraw (.program command) state)).support at member
  have exactMember := drawCutoffLaw_supported attempts _ _ member
  simp only [sharedInternalSourceDraw] at exactMember
  split at exactMember
  · simp only [Draw.map_distribution, oracleFamilyDraw, familyDraw, lowerRequest, physicalRequest,
      Draw.map_distribution, PMF.map_comp, Function.comp_def] at exactMember
    obtain ⟨permutation, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp exactMember
    cases same
    have growth := ProgrammedPermutation.program_resources
      (state.family.permutations (sharedPhysicalIndex (.inl command.1))) (blockFin command.2.1)
      (blockFin command.2.2) permutation reached
    refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
    · intro index
      by_cases equal : index = sharedPhysicalIndex (.inl command.1)
      · subst index
        simp only [Function.update_self]
        exact growth.1.trans (Nat.add_le_add_right (bounded.1 _) 1)
      · simp only [Function.update_of_ne equal]
        exact (bounded.1 index).trans (Nat.le_succ limit)
    · intro index
      by_cases equal : index = sharedPhysicalIndex (.inl command.1)
      · subst index
        simp only [Function.update_self, growth.2]
        exact Nat.add_le_add_right (bounded.2.1 _) 1
      · simp only [Function.update_of_ne equal]
        exact (bounded.2.1 index).trans (Nat.le_succ limit)
    · intro index
      exact (recordHistoryPairs_program_length state.metadata command index).trans
        (Nat.add_le_add_right (bounded.2.2 index) 1)
  · simp only [Draw.distribution, PMF.mem_support_pure_iff, Prod.mk.injEq, true_and] at exactMember
    subst next
    exact ⟨bounded.mono (Nat.le_succ limit), rfl⟩

/-- A command list adds at most its length to the source count limit. -/
theorem sharedCommandListCutoff_growth (attempts limit : Nat) (commands : List SharedCommand)
    (state next : SharedOracleSource) (bounded : SharedSourceCounts state limit)
    (member : some ((), next) ∈ (sharedCommandListCutoff attempts commands state).support) :
    SharedSourceCounts next (limit + commands.length) ∧ next.family.hash = state.family.hash := by
  induction commands generalizing limit state with
  | nil =>
      simp only [sharedCommandListCutoff, PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq, true_and] at member
      subst next
      exact ⟨bounded, rfl⟩
  | cons command rest ih =>
      obtain ⟨head, reached, tail⟩ := (mem_support_bindCutoff _ _ _).mp member
      have step := sharedSourceCommand_growth attempts limit state head.2 command bounded reached
      have final := ih (limit + 1) head.2 step.1 tail
      refine ⟨?_, final.2.trans step.2⟩
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using final.1

end
end Kriterion.ArgoMAC.ArithmeticSimulator
