import Proof.Privacy.Source.SharedQueryCounts
import Proof.Privacy.Collision.SharedPrequeryBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
noncomputable section

/-- A distinct queried domain has a distinct position in the actual transcript. -/
theorem sharedQueryDomain_card_le [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) (index : Shared.FixedKeyIndex) :
    Fintype.card (SharedQueryDomain history index) ≤ history.length := by
  classical
  have witness (query : SharedQueryDomain history index) :
      ∃ position : Fin history.length, (history.get position).domain = query.1 := by
    obtain ⟨record, member, _, domain⟩ := query.2
    obtain ⟨position, same⟩ := List.mem_iff_get.mp member
    exact ⟨position, (congrArg PermutationRecord.domain same).trans domain⟩
  let position := fun query => Classical.choose (witness query)
  have selected (query : SharedQueryDomain history index) :
      (history.get (position query)).domain = query.1 := Classical.choose_spec (witness query)
  have injective : Function.Injective position := by
    intro first second equal
    apply Subtype.ext
    exact (selected first).symm.trans ((congrArg (fun entry => (history.get entry).domain) equal).trans
      (selected second))
  exact (Fintype.card_le_of_injective position injective).trans_eq (Fintype.card_fin _)

/-- Residual queries also fit in the actual transcript length. -/
theorem sharedResidualQueryDomain_card_le [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (covered : Shared.FixedKeyIndex → Set Block) (index : Shared.FixedKeyIndex) :
    Fintype.card (ResidualQueryDomain history covered index) ≤ history.length := by
  classical
  exact (Fintype.card_le_of_injective
    (fun query : ResidualQueryDomain history covered index => query.1) Subtype.val_injective).trans
      (sharedQueryDomain_card_le history index)

/-- The source and query counts fit each permutation throughout the small-budget proof. -/
theorem sharedQueryBudget_fits [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (covered : Shared.FixedKeyIndex → Set Block) (budget : history.length ≤ 2 ^ 101)
    (index : Shared.FixedKeyIndex) :
    sharedCircuitBucketSize index + Fintype.card (SharedQueryDomain history index) ≤ Fintype.card Block ∧
    sharedCircuitBucketSize index + Fintype.card (ResidualQueryDomain history covered index) ≤ Fintype.card Block := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  have source := sharedCircuitBucketSize_le index
  have queries := sharedQueryDomain_card_le history index
  have residual := sharedResidualQueryDomain_card_le history covered index
  rw [card]
  constructor <;> omega

end
end Kriterion.ArgoMAC.Security
