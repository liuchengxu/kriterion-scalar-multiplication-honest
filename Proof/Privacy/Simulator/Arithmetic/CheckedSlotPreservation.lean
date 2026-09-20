import Proof.Privacy.Simulator.Arithmetic.CheckedSlotFinishFamily
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSaved

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle
set_option maxRecDepth 2048

/-- The command prefix retains all three saved command words. -/
theorem checkedSlotPrepared_saved (memory : Memory) (count : Nat) :
    (checkedSlotPrepared count memory).ram 26 = memory.registers 8 ∧
    (checkedSlotPrepared count memory).ram 27 = memory.registers 9 ∧
    (checkedSlotPrepared count memory).ram 28 = memory.ram 14 := by
  have same := (historyFreshSource_data count (executeLinear checkedSlotStart memory)).1
  change (checkedSlotPrepared count memory).ram = _ at same
  rw [same]
  exact ⟨(checkedSlotStart_values memory).1, (checkedSlotStart_values memory).2.1,
    (checkedSlotStart_values memory).2.2.1⟩

/-- One successful finish preserves the base cap and increases the overlay cap by one. -/
theorem checkedSlotProgrammedState_counts (state : SparseOracleFamily) (oracle : Fin 15748)
    (current target : Fin (2 ^ 128)) (baseLimit overlayLimit : Nat)
    (baseBound : ∀ index, (state.permutations index).base.used ≤ baseLimit)
    (overlayBound : ∀ index, (state.permutations index).overlay.length ≤ overlayLimit) :
    (∀ index, ((checkedSlotProgrammedState state oracle current target).permutations index).base.used ≤ baseLimit) ∧
    (∀ index, ((checkedSlotProgrammedState state oracle current target).permutations index).overlay.length ≤ overlayLimit + 1) := by
  constructor
  · intro index
    by_cases same : index = oracle
    · subst index; simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_self] using baseBound oracle
    · simpa only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_of_ne same] using baseBound index
  · intro index
    by_cases same : index = oracle
    · subst index
      simp only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_self,
        List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
      exact Nat.add_le_add_right (overlayBound oracle) 1
    · simp only [checkedSlotProgrammedState, SparseOracleFamily.updatePermutation, Function.update_of_ne same]
      exact le_trans (overlayBound index) (Nat.le_succ _)

/-- Every complete checked command retains a finite family and its selected visible history. -/
theorem checkedSlotSamples_preserves [BN254.FieldCertificate]
    (attempts count : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (pairs : List (Word × Word)) (limit : Nat)
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (history : HistoryMemory memory.ram oracle.castSucc pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (targetValue : memory.ram 14 = BitVec.ofNat 256 target.val)
    (baseRoom : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (overlayRoom : 256 + 2 * ((state.permutations oracle).overlay.length + 1) < 2 ^ 110)
    (historyRoom : 256 + 2 * (pairs.length + 1) < 2 ^ 110)
    (baseBound : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayBound : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotSamples attempts (state.permutations oracle).base.used
      (state.permutations oracle).overlay.length count memory).support) :
    ∃ next : SparseOracleFamily, ∃ nextPairs : List (Word × Word),
      OracleFamilyMemory result.2.1.ram next ∧ OracleFamilyFits next ∧
      HistoryMemory result.2.1.ram oracle.castSucc nextPairs ∧
      (∀ index, (next.permutations index).base.used ≤ limit + 1) ∧
      (∀ index, (next.permutations index).overlay.length ≤ limit + 1) ∧
      nextPairs.length ≤ pairs.length + 1 := by
  obtain ⟨⟨label, final, cost⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  subst result
  let prepared := checkedSlotPrepared count memory
  have preparedPublic : ∀ other region offset, offset < 2 ^ 110 →
      prepared.ram (oracleAddress other region offset) = memory.ram (oracleAddress other region offset) := by
    intro other region offset bound
    change (historyFreshSource count (executeLinear checkedSlotStart memory)).1.ram _ = _
    rw [(historyFreshSource_data count (executeLinear checkedSlotStart memory)).1]
    exact checkedSlotStart_public memory other region offset bound
  have preparedFamily : OracleFamilyMemory prepared.ram state :=
    OracleFamilyMemory.congr memory.ram prepared.ram state represented fits preparedPublic
  have preparedHistory : HistoryMemory prepared.ram oracle.castSucc pairs :=
    HistoryMemory.congr memory.ram prepared.ram oracle.castSucc pairs history (by omega) (preparedPublic oracle.castSucc 3)
  change (label, final, cost) ∈ (checkedSlotBranchSamples attempts _ _ prepared).support at member
  unfold checkedSlotBranchSamples at member
  split at member
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl, rfl⟩ := member
    have collisionPublic : ∀ other region offset, offset < 2 ^ 110 →
        (executeLinear checkedSlotCollision prepared).ram (oracleAddress other region offset) =
          prepared.ram (oracleAddress other region offset) := by
      intro other region offset bound
      rw [checkedSlotCollision_ram]
      exact Function.update_of_ne (oracleAddress_private_disjoint other region offset 31 bound (by decide)) _ _
    refine ⟨state, pairs, OracleFamilyMemory.congr prepared.ram _ state preparedFamily fits collisionPublic, fits,
      HistoryMemory.congr prepared.ram _ oracle.castSucc pairs preparedHistory (by omega) (collisionPublic oracle.castSucc 3), ?_, ?_, by omega⟩
    · intro other; exact le_trans (baseBound other) (Nat.le_succ _)
    · intro other; exact le_trans (overlayBound other) (Nat.le_succ _)
  · obtain ⟨⟨before, spent⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj equal |>.imp_right Prod.mk.inj
    let restored := checkedSlotRestored prepared
    let tail := (internalForwardTail (state.permutations oracle).overlay.length before).1
    have restoredFamily : OracleFamilyMemory restored.ram state := preparedFamily
    have restoredHistory : HistoryMemory restored.ram oracle.castSucc pairs := preparedHistory
    have restoredIndex : restored.registers 9 = BitVec.ofNat 256 oracle.val :=
      (checkedSlotPreparedRestored_data memory count).1.trans index
    have restoredOperand : restored.registers 8 = BitVec.ofNat 256 input.val :=
      (checkedSlotPreparedRestored_data memory count).2.1.trans operand
    have queried : (tail, spent - 1 + (internalForwardTail (state.permutations oracle).overlay.length before).2) ∈
        (internalForwardSamples attempts (state.permutations oracle).base.used
          (state.permutations oracle).overlay.length restored).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(before, spent), reached, rfl⟩
    let next := state.updatePermutation oracle (internalForwardMemoryState (state.permutations oracle) input tail)
    have nextFamily : OracleFamilyMemory tail.ram next :=
      internalForwardSamples_family attempts restored tail _ state oracle input restoredFamily fits
        restoredIndex restoredOperand baseRoom queried
    have nextFits : OracleFamilyFits next := internalForwardFamily_fits state oracle input tail fits (by omega)
    have nextHistory : HistoryMemory tail.ram oracle.castSucc pairs :=
      internalForwardSamples_historyMemory attempts _ _ restored tail _ oracle.castSucc pairs queried
        restoredHistory restoredIndex (restoredFamily.permutations oracle).base.count (by omega) (by omega)
    have nextBase : ∀ other, (next.permutations other).base.used ≤ limit + 1 :=
      internalForwardFamily_count state oracle input tail limit baseBound
    have nextOverlay : ∀ other, (next.permutations other).overlay.length ≤ limit :=
      internalForwardFamily_overlayCount state oracle input tail limit overlayBound
    by_cases failed : before.registers 7 = 0
    · simp only [checkedSlotForwardResult, if_pos failed]
      refine ⟨next, pairs, nextFamily, nextFits, nextHistory, nextBase, ?_, by omega⟩
      intro other; exact le_trans (nextOverlay other) (Nat.le_succ _)
    · have accepted : tail.registers 7 ≠ 0#256 := by
        rw [(internalForwardTail_data (state.permutations oracle).overlay.length before).2.2]
        exact failed
      obtain ⟨current, currentValue⟩ := internalForwardSamples_valueWitness attempts restored tail _ oracle.castSucc
        (state.permutations oracle) input (restoredFamily.permutations oracle) restoredIndex restoredOperand
        (by omega) (fits.overlay oracle) queried accepted
      have keptInput : tail.ram 26 = restored.ram 26 := internalForwardSamples_private attempts _ _ restored tail _ queried
        oracle.castSucc 26 (by decide) (by decide) restoredIndex (restoredFamily.permutations oracle).base.count (by omega)
      have keptTarget : tail.ram 28 = restored.ram 28 := internalForwardSamples_private attempts _ _ restored tail _ queried
        oracle.castSucc 28 (by decide) (by decide) restoredIndex (restoredFamily.permutations oracle).base.count (by omega)
      have savedInput : tail.ram 26 = BitVec.ofNat 256 input.val :=
        keptInput.trans ((checkedSlotPrepared_saved memory count).1.trans operand)
      have savedTarget : tail.ram 28 = BitVec.ofNat 256 target.val :=
        keptTarget.trans ((checkedSlotPrepared_saved memory count).2.2.trans targetValue)
      have nextRoom : 256 + 2 * ((next.permutations oracle).overlay.length + 1) < 2 ^ 110 := by
        simpa only [next, SparseOracleFamily.updatePermutation, Function.update_self,
          (internalForwardMemoryState_growth _ input tail).2] using overlayRoom
      have finalRelations := checkedSlotFinished_family_history tail next oracle current input target pairs nextFamily nextFits
        nextHistory (internalForwardSamples_header attempts _ _ restored tail _ queried oracle.castSucc restoredIndex
          (restoredFamily.permutations oracle).base.count (by omega)) currentValue savedInput savedTarget nextRoom historyRoom
      have finalCounts := checkedSlotProgrammedState_counts next oracle current target (limit + 1) limit nextBase nextOverlay
      simp only [checkedSlotForwardResult, if_neg failed]
      refine ⟨checkedSlotProgrammedState next oracle current target,
        pairs ++ [(BitVec.ofNat 256 input.val, BitVec.ofNat 256 target.val)],
        finalRelations.1, checkedSlotProgrammedState_fits next oracle current target nextFits nextRoom,
        finalRelations.2, finalCounts.1, finalCounts.2, ?_⟩
      simp

end Kriterion.ArgoMAC.ArithmeticSimulator
