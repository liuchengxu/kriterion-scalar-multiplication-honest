import Construction.Simulator.MemoryLayout
import Construction.SharedGarbling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The shared fixed-key interface has 15240 public permutations. -/
theorem sharedFixedKeyIndex_count : Fintype.card Shared.FixedKeyIndex = 15240 := by
  let split : Shared.FixedKeyIndex ≃
      Pipeline.FixedKeyKind × Fin coordinateBitCount × Fin 3 := {
    toFun := fun index => (index.kind, index.position, index.slot)
    invFun := fun value => ⟨value.1, value.2.1, value.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have kinds : Fintype.card Pipeline.FixedKeyKind = 20 := by decide
  rw [Fintype.card_congr split]
  simp [coordinateBitCount, kinds]

/-- The complete public interface fits the reserved oracle index type. -/
theorem publicOracle_count :
    Fintype.card Shared.FixedKeyIndex + Fintype.card EncPRF.PermutationIndex + 1 = 15749 := by
  have coordinate : Fintype.card EncPRF.Coordinate = 2 := by decide
  simp [sharedFixedKeyIndex_count, EncPRF.PermutationIndex, coordinateBitCount, coordinate]

/-- The small-query regime leaves room for all stored pairs and metadata. -/
theorem oracleTable_capacity (queries : Nat) (small : queries < 2 ^ 101) :
    2 * (queries + 836423) + 256 < 2 ^ 110 := by
  norm_num at small ⊢
  omega

/-- The four table regions fit in one oracle region. -/
theorem oracleCell_bounds (oracle : Fin 15749) (table : Fin 4) (offset : Nat)
    (fits : offset < 2 ^ 110) :
    2 ^ 128 ≤ oracleCell oracle table offset ∧ oracleCell oracle table offset < 2 ^ 129 := by
  have indexBound := oracle.isLt
  have tableBound := table.isLt
  unfold oracleCell
  norm_num at fits ⊢
  omega

/-- The word address retains the full table address. -/
theorem oracleAddress_value (oracle : Fin 15749) (table : Fin 4) (offset : Nat)
    (fits : offset < 2 ^ 110) :
    (oracleAddress oracle table offset).toNat = oracleCell oracle table offset := by
  rw [oracleAddress, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact lt_trans (oracleCell_bounds oracle table offset fits).2 (by decide)

/-- Separate table cells cannot share one machine address. -/
theorem oracleAddress_injective (first second : Fin 15749) (left right : Fin 4)
    (start finish : Nat) (startFits : start < 2 ^ 110) (finishFits : finish < 2 ^ 110)
    (equal : oracleAddress first left start = oracleAddress second right finish) :
    first = second ∧ left = right ∧ start = finish := by
  have values := congrArg BitVec.toNat equal
  rw [oracleAddress_value first left start startFits,
    oracleAddress_value second right finish finishFits] at values
  have leftBound := left.isLt
  have rightBound := right.isLt
  unfold oracleCell at values
  norm_num at startFits finishFits values
  have indices : first.val = second.val := by omega
  have tables : left.val = right.val := by omega
  exact ⟨Fin.ext indices, Fin.ext tables, by omega⟩

/-- Public table writes cannot change temporary or private cells. -/
theorem oracleAddress_private_disjoint (oracle : Fin 15749) (table : Fin 4) (offset cell : Nat)
    (fits : offset < 2 ^ 110) (privateBound : cell < 2 ^ 96) :
    oracleAddress oracle table offset ≠ BitVec.ofNat 256 cell := by
  intro equal
  have values := congrArg BitVec.toNat equal
  rw [oracleAddress_value oracle table offset fits, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans privateBound (by decide : 2 ^ 96 < 2 ^ 256))] at values
  have lower := (oracleCell_bounds oracle table offset fits).1
  norm_num at privateBound lower
  omega

/-- Private source storage starts after every temporary cell. -/
theorem privateBase_after_scratch : scratchLimit < privateBase := by decide

end Kriterion.ArgoMAC.ArithmeticSimulator
