import Proof.Privacy.Simulator.Arithmetic.CompiledQueryCoupling
import Proof.Privacy.Simulator.Arithmetic.SharedPublicGrowth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- The physical family supplies every public branch loop count. -/
theorem recordedPublicInputMemory_counts (attempts : Nat) (memory : Memory) (source : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram source.family) (capacity : OracleFamilyFits source.family)
    (room : ∀ oracle, 2 * ((source.family.permutations oracle).base.used + 1) ≤ 2 ^ 110) :
    PublicBranchCounts (publicHandlerKind request) attempts (publicSourceCount source request)
      (publicSourceOverlay source request) (recordedPublicInputMemory memory request rest) := by
  have stored := recordedPublicInputMemory_family memory request rest source.family represented capacity
  have values := recordedPublicInputMemory_values memory request rest
  cases request with
  | fixedForward index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have selected : (recordedPublicInputMemory memory (.fixedForward index value) rest).registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed]
      exact publicHandler_forwardCounts attempts _ oracle.castSucc _ _ (stored.permutations oracle).base
        (stored.permutations oracle).overlay selected (room oracle)
  | encForward index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have selected : (recordedPublicInputMemory memory (.encForward index value) rest).registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_enc, Nat.add_comm]
      exact publicHandler_forwardCounts attempts _ oracle.castSucc _ _ (stored.permutations oracle).base
        (stored.permutations oracle).overlay selected (room oracle)
  | fixedInverse index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have selected : (recordedPublicInputMemory memory (.fixedInverse index value) rest).registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed]
      exact publicHandler_inverseCounts attempts _ oracle.castSucc _ _ (stored.permutations oracle).base
        (stored.permutations oracle).overlay selected
  | encInverse index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have selected : (recordedPublicInputMemory memory (.encInverse index value) rest).registers 9 = BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_enc, Nat.add_comm]
      exact publicHandler_inverseCounts attempts _ oracle.castSucc _ _ (stored.permutations oracle).base
        (stored.permutations oracle).overlay selected
  | hash key =>
      have law := publicHandler_hashCounts attempts 0 _ 15748 _ stored.hash values.2.1
      simpa only [hashWordPairs, List.length_map, publicHandlerKind, publicSourceCount, publicSourceOverlay] using law

/-- The source count cap bounds every selected public table. -/
theorem publicSourceCounts_le (source : SharedOracleSource) (request : SharedQuery) (limit : Nat)
    (bounded : SharedSourceCounts source limit) (hashBound : source.family.hash.length ≤ limit) :
    publicSourceCount source request ≤ limit ∧ publicSourceOverlay source request ≤ limit := by
  cases request with
  | fixedForward index value => exact ⟨bounded.1 _, bounded.2.1 _⟩
  | fixedInverse index value => exact ⟨bounded.1 _, bounded.2.1 _⟩
  | encForward index value => exact ⟨bounded.1 _, bounded.2.1 _⟩
  | encInverse index value => exact ⟨bounded.1 _, bounded.2.1 _⟩
  | hash key => exact ⟨hashBound, Nat.zero_le _⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
