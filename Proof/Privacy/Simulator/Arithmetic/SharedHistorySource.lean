import Proof.Privacy.Simulator.Arithmetic.CheckedSlotGlobalPreservation
import Proof.Privacy.Simulator.Arithmetic.SharedFamilySource
import Proof.Privacy.Simulator.Arithmetic.HistoryFreshSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine
noncomputable section
set_option maxRecDepth 4096

/-- The machine stores each block in its canonical 256-bit word. -/
def historyWord (block : Block) : Word := BitVec.ofNat 256 block.toNat

/-- The history word encoding is injective. -/
theorem historyWord_injective : Function.Injective historyWord := by
  intro left right equal
  apply BitVec.eq_of_toNat_eq
  have values := congrArg BitVec.toNat equal
  simpa only [historyWord, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans left.isLt (by decide : 2 ^ 128 < 2 ^ 256)),
    Nat.mod_eq_of_lt (lt_trans right.isLt (by decide : 2 ^ 128 < 2 ^ 256))] using values

/-- The stored history orders each selected transcript from first record to last record. -/
def recordHistoryPairs {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (index : Index) : List (Word × Word) :=
  ((history.filter fun record => record.index = index).reverse).map
    (fun record => (historyWord record.domain, historyWord record.range))

/-- One new selected transcript record appends one physical history pair. -/
theorem recordHistoryPairs_cons {Index : Type} [DecidableEq Index]
    (record : PermutationRecord Index Block) (history : List (PermutationRecord Index Block)) (index : Index) :
    recordHistoryPairs (record :: history) index =
      if record.index = index then recordHistoryPairs history index ++ [(historyWord record.domain, historyWord record.range)]
      else recordHistoryPairs history index := by
  by_cases same : record.index = index <;> simp [recordHistoryPairs, same]

/-- The two physical history scans test the exact transcript freshness predicate. -/
theorem recordHistoryPairs_fresh {Index : Type} [DecidableEq Index]
    (history : List (PermutationRecord Index Block)) (index : Index) (domain range : Block) :
    ((∀ pair ∈ recordHistoryPairs history index, pair.1 ≠ historyWord domain) ∧
      (∀ pair ∈ recordHistoryPairs history index, pair.2 ≠ historyWord range)) ↔
      FreshPermutationPair history index domain range := by
  constructor
  · intro fresh record member selected
    have stored : (historyWord record.domain, historyWord record.range) ∈ recordHistoryPairs history index := by
      apply List.mem_map.mpr
      refine ⟨record, ?_, rfl⟩
      simpa only [List.mem_reverse, List.mem_filter, decide_eq_true_eq] using And.intro member selected
    exact ⟨fun same => fresh.1 _ stored (congrArg historyWord same),
      fun same => fresh.2 _ stored (congrArg historyWord same)⟩
  · intro fresh
    constructor <;> intro pair member
    all_goals
      obtain ⟨record, inRecords, samePair⟩ := List.mem_map.mp member
      subst pair
      simp only [List.mem_reverse, List.mem_filter, decide_eq_true_eq] at inRecords
    · exact fun same => (fresh record inRecords.1 inRecords.2).1 (historyWord_injective same)
    · exact fun same => (fresh record inRecords.1 inRecords.2).2 (historyWord_injective same)

/-- The freshness scan returns a canonical Boolean flag. -/
theorem historyFreshSource_flag (count : Nat) (memory : Memory) :
    (historyFreshSource count memory).1.registers 7 = 0 ∨ (historyFreshSource count memory).1.registers 7 = 1 := by
  have flag := tableScan_flag count (tableInitial (historyRangeReady (historyDomainScan count memory).1))
  change (historyRangeScan count (historyDomainScan count memory).1).1.registers 12 = 0 ∨
    (historyRangeScan count (historyDomainScan count memory).1).1.registers 12 = 1 at flag
  simp only [historyFreshSource]
  split
  · rcases flag with zero | one
    · right
      change (historyRangeScan count (historyDomainScan count memory).1).1.registers 12 ^^^ 1 = 1
      rw [zero]
      decide
    · left
      change (historyRangeScan count (historyDomainScan count memory).1).1.registers 12 ^^^ 1 = 0
      rw [one]
      decide
  · left; rfl

/-- The shared source metadata has the exact fixed history stored in RAM. -/
def SharedHistoryMemory (ram : Word → Word) (metadata : Metadata) : Prop :=
  ∀ index : Shared.FixedKeyIndex, HistoryMemory ram (sharedPhysicalIndex (.inl index)).castSucc
    (recordHistoryPairs metadata.fixedTranscript index)

/-- The actual checked command accepts exactly the shared source's freshness check. -/
theorem checkedSlotPrepared_sharedFresh (memory : Memory) (metadata : Metadata)
    (index : Shared.FixedKeyIndex) (domain range : Block)
    (represented : SharedHistoryMemory memory.ram metadata)
    (selected : memory.registers 9 = BitVec.ofNat 256 (sharedPhysicalIndex (.inl index)).val)
    (operand : memory.registers 8 = historyWord domain) (target : memory.ram 14 = historyWord range)
    (capacity : 256 + 2 * (recordHistoryPairs metadata.fixedTranscript index).length < 2 ^ 110) :
    (checkedSlotPrepared (recordHistoryPairs metadata.fixedTranscript index).length memory).registers 7 ≠ 0 ↔
      freshPermutationPairCheck metadata.fixedTranscript index domain range = true := by
  let started := executeLinear checkedSlotStart memory
  have header : started.registers 6 = oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 0 0 := by
    have selectedPhysical : memory.registers 9 =
        BitVec.ofNat 256 (sharedPhysicalIndex (.inl index)).castSucc.val := by
      simpa only [Fin.val_castSucc] using selected
    exact ((checkedSlotStart_values memory).2.2.2.1).trans
      ((congrArg oracleHeader selectedPhysical).trans (oracleHeader_address _))
  have stored : HistoryMemory started.ram (sharedPhysicalIndex (.inl index)).castSucc
      (recordHistoryPairs metadata.fixedTranscript index) :=
    HistoryMemory.congr memory.ram started.ram _ _ (represented index) capacity
      (checkedSlotStart_public memory _ 3)
  have base : historyHeader started + 256#256 = oracleAddress (sharedPhysicalIndex (.inl index)).castSucc 3 256 := by
    rw [historyHeader_address started _ header]
    exact oracleAddress_add _ 3 0 256
  have source := historyFreshSource_accepts (recordHistoryPairs metadata.fixedTranscript index) started
    (by rw [base]; exact stored.stored)
  have startedOperand : started.registers 8 = historyWord domain := (checkedSlotStart_values memory).2.2.2.2.1.trans operand
  have startedTarget : started.ram 14 = historyWord range := by
    rw [checkedSlotStart_ram]
    simp only [Function.update_of_ne (by decide : (14 : Word) ≠ 28),
      Function.update_of_ne (by decide : (14 : Word) ≠ 27), Function.update_of_ne (by decide : (14 : Word) ≠ 26)]
    exact target
  rw [startedOperand, startedTarget, recordHistoryPairs_fresh, ← freshPermutationPairCheck_eq_true] at source
  have flag := historyFreshSource_flag (recordHistoryPairs metadata.fixedTranscript index).length started
  change (historyFreshSource (recordHistoryPairs metadata.fixedTranscript index).length started).1.registers 7 ≠ 0 ↔ _
  rw [← source]
  rcases flag with zero | one
  · simp only [zero]; decide
  · simp only [one]; decide

end
end Kriterion.ArgoMAC.ArithmeticSimulator
