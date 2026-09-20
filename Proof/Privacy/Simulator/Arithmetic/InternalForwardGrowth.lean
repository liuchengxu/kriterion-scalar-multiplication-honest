import Proof.Privacy.Simulator.Arithmetic.InternalForwardFamily

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- A recovered sparse query adds at most one table entry. -/
theorem sparseForwardNext_used {size : Nat} (state : SparsePermutation size) (input output : Fin size) :
    (sparseForwardNext state input output).used ≤ state.used + 1 := by
  unfold sparseForwardNext
  split
  · exact Nat.le_succ _
  · simp [SparsePermutation.extend]

/-- A programmed query adds at most one base entry and preserves all programmed swaps. -/
theorem programmedForwardNext_growth (state : ProgrammedPermutation (2 ^ 128))
    (input output : Fin (2 ^ 128)) :
    (programmedForwardNext state input output).base.used ≤ state.base.used + 1 ∧
    (programmedForwardNext state input output).overlay = state.overlay :=
  ⟨sparseForwardNext_used _ _ _, rfl⟩

/-- The internal observer retains the same bound on both acceptance and cutoff paths. -/
theorem internalForwardMemoryState_growth (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) :
    (internalForwardMemoryState state input memory).base.used ≤ state.base.used + 1 ∧
    (internalForwardMemoryState state input memory).overlay = state.overlay := by
  unfold internalForwardMemoryState
  cases answer : queryValue memory with
  | none => exact ⟨Nat.le_succ _, rfl⟩
  | some word => exact programmedForwardNext_growth _ _ _

/-- One internal query increases a common family count cap by at most one. -/
theorem internalForwardFamily_count (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (memory : Memory) (limit : Nat)
    (bounded : ∀ index, (state.permutations index).base.used ≤ limit) :
    ∀ index, ((state.updatePermutation oracle
      (internalForwardMemoryState (state.permutations oracle) input memory)).permutations index).base.used ≤ limit + 1 := by
  intro index
  by_cases same : index = oracle
  · subst index
    simp only [SparseOracleFamily.updatePermutation, Function.update_self]
    exact le_trans (internalForwardMemoryState_growth _ _ _).1 (Nat.add_le_add_right (bounded oracle) 1)
  · simp only [SparseOracleFamily.updatePermutation, Function.update_of_ne same]
    exact le_trans (bounded index) (Nat.le_succ _)

/-- Every internal query preserves a common bound on the programmed swap counts. -/
theorem internalForwardFamily_overlayCount (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (memory : Memory) (limit : Nat)
    (bounded : ∀ index, (state.permutations index).overlay.length ≤ limit) :
    ∀ index, ((state.updatePermutation oracle
      (internalForwardMemoryState (state.permutations oracle) input memory)).permutations index).overlay.length ≤ limit := by
  intro index
  by_cases same : index = oracle
  · subst index
    simp only [SparseOracleFamily.updatePermutation, Function.update_self]
    rw [(internalForwardMemoryState_growth (state.permutations oracle) input memory).2]
    exact bounded oracle
  · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using bounded index

/-- The complete family retains its capacity invariant after one internal query. -/
theorem internalForwardFamily_fits (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (memory : Memory) (capacity : OracleFamilyFits state)
    (fits : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110) :
    OracleFamilyFits (state.updatePermutation oracle
      (internalForwardMemoryState (state.permutations oracle) input memory)) := by
  constructor
  · intro index
    by_cases same : index = oracle
    · subst index
      simp only [SparseOracleFamily.updatePermutation, Function.update_self]
      have bound := (internalForwardMemoryState_growth (state.permutations oracle) input memory).1
      omega
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using capacity.base index
  · intro index
    by_cases same : index = oracle
    · subst index
      simpa only [SparseOracleFamily.updatePermutation, Function.update_self,
        (internalForwardMemoryState_growth _ input memory).2] using capacity.overlay oracle
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using capacity.overlay index
  · exact capacity.hash

end Kriterion.ArgoMAC.ArithmeticSimulator
