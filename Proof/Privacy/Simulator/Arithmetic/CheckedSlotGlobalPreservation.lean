import Proof.Privacy.Simulator.Arithmetic.CheckedSlotOtherHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The RAM stores a separate ordered visible history for every physical oracle. -/
def OracleHistoryMemory (ram : Word → Word) (history : Fin 15749 → List (Word × Word)) : Prop :=
  ∀ oracle, HistoryMemory ram oracle (history oracle)

/-- Every checked command preserves all source tables and all visible histories. -/
theorem checkedSlotSamples_global_preserves [BN254.FieldCertificate]
    (attempts count : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (histories : Fin 15749 → List (Word × Word)) (limit : Nat)
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (history : OracleHistoryMemory memory.ram histories)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (targetValue : memory.ram 14 = BitVec.ofNat 256 target.val)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (baseBound : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayBound : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (historyBound : ∀ index, (histories index).length ≤ limit)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotSamples attempts (state.permutations oracle).base.used
      (state.permutations oracle).overlay.length count memory).support) :
    ∃ next : SparseOracleFamily, ∃ nextHistories : Fin 15749 → List (Word × Word),
      OracleFamilyMemory result.2.1.ram next ∧ OracleFamilyFits next ∧
      OracleHistoryMemory result.2.1.ram nextHistories ∧
      (∀ index, (next.permutations index).base.used ≤ limit + 1) ∧
      (∀ index, (next.permutations index).overlay.length ≤ limit + 1) ∧
      (∀ index, (nextHistories index).length ≤ limit + 1) := by
  have baseRoom : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110 := by
    have := baseBound oracle
    omega
  have overlayRoom : 256 + 2 * ((state.permutations oracle).overlay.length + 1) < 2 ^ 110 := by
    have := overlayBound oracle
    omega
  have historyRoom : 256 + 2 * ((histories oracle.castSucc).length + 1) < 2 ^ 110 := by
    have := historyBound oracle.castSucc
    omega
  obtain ⟨next, nextPairs, nextFamily, nextFits, nextHistory, nextBase, nextOverlay, nextLength⟩ :=
    checkedSlotSamples_preserves attempts count memory state oracle input target (histories oracle.castSucc) limit
      represented fits (history oracle.castSucc) index operand targetValue baseRoom overlayRoom historyRoom
      baseBound overlayBound result supported
  refine ⟨next, Function.update histories oracle.castSucc nextPairs, nextFamily, nextFits, ?_, nextBase, nextOverlay, ?_⟩
  · intro other
    by_cases same : other = oracle.castSucc
    · subst other
      simpa only [Function.update_self] using nextHistory
    · simp only [Function.update_of_ne same]
      apply HistoryMemory.congr memory.ram result.2.1.ram other (histories other) (history other)
      · have := historyBound other; omega
      · intro offset offsetFits
        exact checkedSlotSamples_otherHistory attempts count (histories oracle.castSucc).length memory
          oracle.castSucc other (state.permutations oracle) (represented.permutations oracle) index
          (history oracle.castSucc).count (by omega) (by omega) (by omega) same offset offsetFits result supported
  · intro other
    by_cases same : other = oracle.castSucc
    · subst other
      simp only [Function.update_self]
      exact le_trans nextLength (Nat.add_le_add_right (historyBound oracle.castSucc) 1)
    · simp only [Function.update_of_ne same]
      exact le_trans (historyBound other) (Nat.le_succ _)

/-- Every automatic checked command retains the same complete finite invariant. -/
theorem checkedSlotAutomaticSamples_global_preserves [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input target : Fin (2 ^ 128)) (histories : Fin 15749 → List (Word × Word)) (limit : Nat)
    (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state)
    (history : OracleHistoryMemory memory.ram histories)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (targetValue : memory.ram 14 = BitVec.ofNat 256 target.val)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (baseBound : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayBound : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (historyBound : ∀ index, (histories index).length ≤ limit)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotAutomaticSamples attempts memory).support) :
    ∃ next : SparseOracleFamily, ∃ nextHistories : Fin 15749 → List (Word × Word),
      OracleFamilyMemory result.2.1.ram next ∧ OracleFamilyFits next ∧
      OracleHistoryMemory result.2.1.ram nextHistories ∧
      (∀ index, (next.permutations index).base.used ≤ limit + 1) ∧
      (∀ index, (next.permutations index).overlay.length ≤ limit + 1) ∧
      (∀ index, (nextHistories index).length ≤ limit + 1) := by
  have counts := checkedSlotCounts_eq memory oracle.castSucc (state.permutations oracle)
    (represented.permutations oracle) index (fits.base oracle) (fits.overlay oracle)
  simp only [checkedSlotAutomaticSamples, counts.1, counts.2] at supported
  exact checkedSlotSamples_global_preserves attempts (checkedSlotHistoryCount memory) memory state oracle input target
    histories limit represented fits history index operand targetValue room baseBound overlayBound historyBound result supported

end Kriterion.ArgoMAC.ArithmeticSimulator
