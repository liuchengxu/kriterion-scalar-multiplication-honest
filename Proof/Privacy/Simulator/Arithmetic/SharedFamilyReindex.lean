import Proof.Privacy.Simulator.Arithmetic.OracleFamilyCutoff
import Proof.Privacy.Simulator.SharedMachineInitial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The named three-slot family has the exact physical permutation index order. -/
def sharedPhysicalIndex : OracleIndex ≃ Fin 15748 :=
  ((Equiv.sumCongr (Fintype.equivFin Shared.FixedKeyIndex) (Fintype.equivFin EncPRF.PermutationIndex)).trans
    finSumFinEquiv).trans (finCongr (by have := publicOracle_count; omega))

/-- The fixed index uses its canonical shared enumeration. -/
theorem sharedPhysicalIndex_fixed (index : Shared.FixedKeyIndex) :
    (sharedPhysicalIndex (.inl index)).val = (Fintype.equivFin Shared.FixedKeyIndex index).val := by
  simp only [sharedPhysicalIndex, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, finCongr, Fin.castAdd, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_castLE]

/-- The encryption index follows all 15240 shared fixed permutations. -/
theorem sharedPhysicalIndex_enc (index : EncPRF.PermutationIndex) :
    (sharedPhysicalIndex (.inr index)).val = 15240 + (Fintype.equivFin EncPRF.PermutationIndex index).val := by
  change Fintype.card Shared.FixedKeyIndex + _ = _
  rw [sharedFixedKeyIndex_count]

/-- The source conversion changes only the oracle index representation. -/
def namedOracleData (state : SparseOracleFamily) : OracleData :=
  (fun index => state.permutations (sharedPhysicalIndex index), state.hash)

/-- The index conversion retains every finite source table. -/
def namedOracleDataEquiv : SparseOracleFamily ≃ OracleData where
  toFun := namedOracleData
  invFun state := ⟨fun index => state.1 (sharedPhysicalIndex.symm index), state.2⟩
  left_inv state := by cases state; simp only [namedOracleData, Equiv.apply_symm_apply]
  right_inv state := by cases state; simp only [namedOracleData, Equiv.symm_apply_apply]

/-- A physical update changes exactly the corresponding named permutation. -/
theorem namedOracleData_update (state : SparseOracleFamily) (index : OracleIndex)
    (next : ProgrammedPermutation (2 ^ 128)) :
    namedOracleData (state.updatePermutation (sharedPhysicalIndex index) next) =
      (Function.update (namedOracleData state).1 index next, state.hash) := by
  apply Prod.ext
  · funext current
    by_cases same : current = index
    · subst current; simp [namedOracleData, SparseOracleFamily.updatePermutation]
    · have different := fun equal => same (sharedPhysicalIndex.injective equal)
      simp only [namedOracleData, SparseOracleFamily.updatePermutation, Function.update_of_ne different,
        Function.update_of_ne same]
  · rfl

/-- Each named request selects its exact physical permutation or hash region. -/
def physicalRequest : lowerSpec.Query → oracleFamilySpec.Query
  | .inl (index, action) => .inl (sharedPhysicalIndex index, action)
  | .inr key => .inr key

/-- Each physical reply has the named request's exact finite answer type. -/
def namedAnswer : (query : lowerSpec.Query) → oracleFamilySpec.Answer (physicalRequest query) → lowerSpec.Answer query
  | .inl _, value => value
  | .inr _, value => value

private theorem draw_map_map {A B C : Type} (draw : Draw A) (first : A → B) (second : B → C) :
    (draw.map first).map second = draw.map (fun value => second (first value)) := by
  cases draw <;> rfl

/-- The physical family source has the exact named family law under index conversion. -/
theorem oracleFamilyDraw_named (query : lowerSpec.Query) (state : SparseOracleFamily) :
    (oracleFamilyDraw (physicalRequest query) state).map
      (fun result => (namedAnswer query result.1, namedOracleData result.2)) =
      lowerDraw query (namedOracleData state) := by
  cases query with
  | inl query =>
      rcases query with ⟨index, action⟩
      simp only [physicalRequest, oracleFamilyDraw, lowerDraw, familyDraw, draw_map_map, namedAnswer, namedOracleData]
      cases action <;> apply congrArg (fun convert => Draw.map convert _) <;> funext result <;>
        apply Prod.ext
      all_goals first | rfl | exact namedOracleData_update state index result.2
  | inr key =>
      simp only [physicalRequest, oracleFamilyDraw, lowerDraw, draw_map_map, namedAnswer,
        namedOracleData, SparseOracleFamily.updateHash]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
