import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJointSource
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicNonfixed

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] sharedPhysicalIndex

/-- Physical source memory supplies the complete public reply invariant. -/
theorem recordedPublicJoint_ready (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (histories : SharedHistoryMemory memory.ram state.metadata)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ index, 257 + 2 * (recordHistoryPairs state.metadata.fixedTranscript index).length < 2 ^ 110) :
    RecordedPublicReplyStable (publicHandlerKind request) attempts (publicSourceCount state request)
      (publicSourceOverlay state request) (recordedPublicInputMemory memory request rest) := by
  have stored := recordedPublicInputMemory_family memory request rest state.family represented capacity
  have values := recordedPublicInputMemory_values memory request rest
  have saved := recordedPublicInputMemory_saved memory request rest
  cases request with
  | fixedForward index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have indexWord : (recordedPublicInputMemory memory (.fixedForward index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      exact recordedPublic_stable .forward attempts _ _
        (recordHistoryPairs state.metadata.fixedTranscript index).length _ oracle.castSucc
        indexWord (stored.permutations oracle).base.count
        ((recordedPublicInputMemory_public memory (.fixedForward index value) rest oracle.castSucc 3 0 (by decide)).trans
          (histories index).count) (room oracle) (historyRoom index)
  | fixedInverse index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have indexWord : (recordedPublicInputMemory memory (.fixedInverse index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      exact recordedPublic_stable .inverse attempts _ _
        (recordHistoryPairs state.metadata.fixedTranscript index).length _ oracle.castSucc
        indexWord (stored.permutations oracle).base.count
        ((recordedPublicInputMemory_public memory (.fixedInverse index value) rest oracle.castSucc 3 0 (by decide)).trans
          (histories index).count) (room oracle) (historyRoom index)
  | encForward index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have indexWord : (recordedPublicInputMemory memory (.encForward index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have tag : (recordedPublicInputMemory memory (.encForward index value) rest).ram 49#256 = 2#256 := saved.2
      exact recordedPublicForward_nonfixedStable attempts _ _ _ oracle.castSucc indexWord
        (stored.permutations oracle).base.count (room oracle)
        (by rw [tag]; decide) (by rw [tag]; decide)
  | encInverse index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have indexWord : (recordedPublicInputMemory memory (.encInverse index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have tag : (recordedPublicInputMemory memory (.encInverse index value) rest).ram 49#256 = 3#256 := saved.2
      exact recordedPublicInverse_nonfixedStable attempts _ _ _ oracle.castSucc indexWord
        (stored.permutations oracle).base.count (room oracle)
        (by rw [tag]; decide) (by rw [tag]; decide)
  | hash key => trivial

/-- The physical public machine and the shared source have the exact same joint reply law. -/
theorem recordedPublicJoint_physicalSource [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SharedOracleSource) (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (histories : SharedHistoryMemory memory.ram state.metadata)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (historyRoom : ∀ index, 257 + 2 * (recordHistoryPairs state.metadata.fixedTranscript index).length < 2 ^ 110)
    (empty : memory.bits 3 = []) :
    (recordedPublicJoint attempts memory state request rest).map Prod.snd =
      sharedSourceCutoff attempts (.inr request) state :=
  recordedPublicJoint_source attempts memory state request rest represented capacity room empty
    (recordedPublicJoint_ready attempts memory state request rest represented capacity histories room historyRoom)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
