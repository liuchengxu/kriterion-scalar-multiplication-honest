import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicFamily
import Proof.Privacy.Simulator.Arithmetic.SharedPublicRecovery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security.OperationalOracle Security.SharedSimulatorMachine

/-- Each public reply adds at most one pair to each fixed history. -/
theorem recordHistoryPairs_record_length (metadata : Metadata) (request : SharedQuery)
    (reply : SharedAnswer request) (index : Shared.FixedKeyIndex) :
    (recordHistoryPairs (metadata.record request reply).fixedTranscript index).length ≤
      (recordHistoryPairs metadata.fixedTranscript index).length + 1 := by
  cases request with
  | fixedForward current value =>
      change (recordHistoryPairs (PermutationRecord.mk .forward .adversary current value reply :: _) index).length ≤ _
      rw [recordHistoryPairs_cons]
      split <;> simp
  | fixedInverse current value =>
      change (recordHistoryPairs (PermutationRecord.mk .inverse .adversary current reply value :: _) index).length ≤ _
      rw [recordHistoryPairs_cons]
      split <;> simp
  | encForward => exact Nat.le_succ _
  | encInverse => exact Nat.le_succ _
  | hash => exact Nat.le_succ _

/-- One read update increases the family count cap by at most one. -/
theorem publicReadFamily_counts (family : SparseOracleFamily) (oracle : Fin 15748)
    (next : ProgrammedPermutation (2 ^ 128)) (limit : Nat)
    (base : ∀ index, (family.permutations index).base.used ≤ limit)
    (overlay : ∀ index, (family.permutations index).overlay.length ≤ limit)
    (growth : next.base.used ≤ (family.permutations oracle).base.used + 1)
    (unchanged : next.overlay = (family.permutations oracle).overlay) :
    (∀ index, ((family.updatePermutation oracle next).permutations index).base.used ≤ limit + 1) ∧
    (∀ index, ((family.updatePermutation oracle next).permutations index).overlay.length ≤ limit + 1) := by
  constructor
  · intro index
    by_cases same : index = oracle
    · subst index
      simpa only [SparseOracleFamily.updatePermutation, Function.update_self] using
        growth.trans (Nat.add_le_add_right (base oracle) 1)
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using (base index).trans (Nat.le_succ limit)
  · intro index
    by_cases same : index = oracle
    · subst index
      simpa only [SparseOracleFamily.updatePermutation, Function.update_self, unchanged] using (overlay oracle).trans (Nat.le_succ limit)
    · simpa only [SparseOracleFamily.updatePermutation, Function.update_of_ne same] using (overlay index).trans (Nat.le_succ limit)

/-- Every recovered public source increases the common count cap by at most one. -/
theorem sharedPublicNext_counts (state : SharedOracleSource) (request : SharedQuery)
    (reply : SharedAnswer request) (limit : Nat) (bounded : SharedSourceCounts state limit) :
    SharedSourceCounts (sharedPublicNext state request reply) (limit + 1) := by
  have history (index) := (recordHistoryPairs_record_length state.metadata request reply index).trans
    (Nat.add_le_add_right (bounded.2.2 index) 1)
  refine ⟨?_, ?_, history⟩
  all_goals
    cases request with
    | fixedForward index value =>
        have growth := programmedForwardNext_growth (state.family.permutations (sharedPhysicalIndex (.inl index))) (blockFin value) (blockFin reply)
        have result := publicReadFamily_counts state.family (sharedPhysicalIndex (.inl index)) _ limit bounded.1 bounded.2.1 growth.1 growth.2
        first | exact result.1 | exact result.2
    | fixedInverse index value =>
        have growth := programmedInverseNext_growth (state.family.permutations (sharedPhysicalIndex (.inl index))) (blockFin value) (blockFin reply)
        have result := publicReadFamily_counts state.family (sharedPhysicalIndex (.inl index)) _ limit bounded.1 bounded.2.1 growth.1 growth.2
        first | exact result.1 | exact result.2
    | encForward index value =>
        have growth := programmedForwardNext_growth (state.family.permutations (sharedPhysicalIndex (.inr index))) (blockFin value) (blockFin reply)
        have result := publicReadFamily_counts state.family (sharedPhysicalIndex (.inr index)) _ limit bounded.1 bounded.2.1 growth.1 growth.2
        first | exact result.1 | exact result.2
    | encInverse index value =>
        have growth := programmedInverseNext_growth (state.family.permutations (sharedPhysicalIndex (.inr index))) (blockFin value) (blockFin reply)
        have result := publicReadFamily_counts state.family (sharedPhysicalIndex (.inr index)) _ limit bounded.1 bounded.2.1 growth.1 growth.2
        first | exact result.1 | exact result.2
    | hash key =>
        intro index
        first | exact (bounded.1 index).trans (Nat.le_succ limit) | exact (bounded.2.1 index).trans (Nat.le_succ limit)

/-- A public hash query adds at most one entry; other public queries keep the table. -/
theorem sharedPublicNext_hashLength (state : SharedOracleSource) (request : SharedQuery)
    (reply : SharedAnswer request) :
    (sharedPublicNext state request reply).family.hash.length ≤ state.family.hash.length + 1 := by
  cases request <;> try exact Nat.le_succ _
  rename_i key
  change (hashNextTable state.family.hash key (hashFin reply)).length ≤ _
  unfold hashNextTable
  split <;> simp

end Kriterion.ArgoMAC.ArithmeticSimulator
