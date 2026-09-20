import Construction.Simulator.SelectedLabelStore
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSource
import Proof.Privacy.Simulator.Arithmetic.DrawMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each store uses fourteen fixed instructions. -/
theorem selectedLabelStore_length (index : Fin 508) : (selectedLabelStore index).length = 14 := by
  simp [selectedLabelStore, labelSelect]

/-- Each store writes exactly one selected label. -/
theorem selectedLabelStore_ram (index : Fin 508) (base : Memory) :
    (executeLinear (selectedLabelStore index) base).ram =
      Function.update base.ram (base.registers 14 + BitVec.ofNat 256 index.val)
        (selectedLabelWord index base) := by
  rw [selectedLabelStore, executeLinear_append]
  change Function.update (executeLinear (labelSelect index) base).ram
    ((executeLinear (labelSelect index) base).registers 14 + BitVec.ofNat 256 index.val)
    ((executeLinear (labelSelect index) base).registers 8) = _
  rw [labelSelect_word, (labelSelect_data index base).1, labelSelect_caller index base 14 (by decide)]

/-- Each store preserves all bit stacks. -/
theorem selectedLabelStore_bits (index : Fin 508) (base : Memory) :
    (executeLinear (selectedLabelStore index) base).bits = base.bits := by
  rw [selectedLabelStore, executeLinear_append]
  simpa only [executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute] using
    (labelSelect_data index base).2

/-- Each store preserves the source and destination pointers. -/
theorem selectedLabelStore_caller (index : Fin 508) (base : Memory) (register : Register)
    (caller : 11 ≤ register.val) :
    (executeLinear (selectedLabelStore index) base).registers register = base.registers register := by
  have different : register ≠ 0 := by intro same; subst register; simp at caller
  rw [selectedLabelStore, executeLinear_append]
  simp only [executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne different]
  exact labelSelect_caller index base register caller

/-- The selector reads one coordinate cell and one key cell for each label. -/
def SelectedReadAddress (reference : Memory) (address : Word) : Prop :=
  ∃ index : Fin 508,
    address = reference.registers 12 + BitVec.ofNat 256 (selectedCoordinate index) ∨
    address = reference.registers 11 +
      (BitVec.ofNat 256 (selectedFalseOffset index) - selectedBitWord index reference)

/-- The current memory preserves all selector inputs and caller pointers. -/
def SelectedReadAgreement (reference current : Memory) : Prop :=
  (∀ register : Register, 11 ≤ register.val → current.registers register = reference.registers register) ∧
  ∀ address, SelectedReadAddress reference address → current.ram address = reference.ram address

/-- Read agreement preserves every selected label. -/
theorem selectedReadAgreement_word (reference current : Memory)
    (agreement : SelectedReadAgreement reference current) (index : Fin 508) :
    selectedLabelWord index current = selectedLabelWord index reference := by
  have bit : selectedBitWord index current = selectedBitWord index reference := by
    unfold selectedBitWord
    rw [agreement.1 12 (by decide), agreement.2 _ ⟨index, Or.inl rfl⟩]
  unfold selectedLabelWord
  rw [agreement.1 11 (by decide), bit, agreement.2 _ ⟨index, Or.inr rfl⟩]

/-- The destination region does not contain any selector input. -/
def SelectedStoreDisjoint (reference : Memory) : Prop :=
  ∀ index : Fin 508, ¬ SelectedReadAddress reference
    (reference.registers 14 + BitVec.ofNat 256 index.val)

/-- A disjoint store preserves all selector inputs. -/
theorem selectedLabelStore_agreement (reference current : Memory)
    (agreement : SelectedReadAgreement reference current) (disjoint : SelectedStoreDisjoint reference)
    (index : Fin 508) :
    SelectedReadAgreement reference (executeLinear (selectedLabelStore index) current) := by
  constructor
  · intro register caller
    rw [selectedLabelStore_caller index current register caller]
    exact agreement.1 register caller
  · intro address reads
    rw [selectedLabelStore_ram, agreement.1 14 (by decide)]
    have different : address ≠ reference.registers 14 + BitVec.ofNat 256 index.val := by
      intro equal
      exact disjoint index (equal ▸ reads)
    rw [Function.update_of_ne different]
    exact agreement.2 address reads

/-- The source writer applies the same selected-label stores. -/
def storeSelectedLabels (pointer : Word) (values : Fin 508 → Word)
    (indices : List (Fin 508)) (ram : Word → Word) : Word → Word :=
  indices.foldl (fun memory index => Function.update memory
    (pointer + BitVec.ofNat 256 index.val) (values index)) ram

/-- The store sequence has the exact source RAM law and preserves its inputs. -/
theorem selectedLabelStores_memory (reference current : Memory)
    (agreement : SelectedReadAgreement reference current) (disjoint : SelectedStoreDisjoint reference)
    (indices : List (Fin 508)) :
    let result := executeLinear (selectedLabelStores indices) current
    result.ram = storeSelectedLabels (reference.registers 14)
      (fun index => selectedLabelWord index reference) indices current.ram ∧
    result.bits = current.bits ∧ SelectedReadAgreement reference result := by
  induction indices generalizing current with
  | nil => simp [selectedLabelStores, executeLinear, storeSelectedLabels, agreement]
  | cons index tail ih =>
    simp only [selectedLabelStores, List.flatMap_cons, executeLinear_append]
    have next := selectedLabelStore_agreement reference current agreement disjoint index
    have result := ih (executeLinear (selectedLabelStore index) current) next
    refine ⟨?_, result.2.1.trans (selectedLabelStore_bits index current), result.2.2⟩
    change (executeLinear (selectedLabelStores tail) (executeLinear (selectedLabelStore index) current)).ram = _
    rw [result.1, selectedLabelStore_ram, agreement.1 14 (by decide),
      selectedReadAgreement_word reference current agreement index]
    rfl

/-- Each stored index has its selected value. Other indices retain their old value. -/
theorem storeSelectedLabels_get (pointer : Word) (values : Fin 508 → Word)
    (indices : List (Fin 508)) (ram : Word → Word) (index : Fin 508) :
    storeSelectedLabels pointer values indices ram (pointer + BitVec.ofNat 256 index.val) =
      if index ∈ indices then values index else ram (pointer + BitVec.ofNat 256 index.val) := by
  induction indices generalizing ram with
  | nil => simp [storeSelectedLabels]
  | cons head tail ih =>
    change storeSelectedLabels pointer values tail
      (Function.update ram (pointer + BitVec.ofNat 256 head.val) (values head)) _ = _
    rw [ih]
    by_cases member : index ∈ tail
    · simp [member]
    · by_cases same : index = head
      · subst head
        simp [member]
      · have distinct : pointer + BitVec.ofNat 256 index.val ≠ pointer + BitVec.ofNat 256 head.val := by
          intro equal
          have vals := (drawAddress_injective pointer index.val head.val
            (lt_trans index.isLt (by decide)) (lt_trans head.isLt (by decide))).mp equal
          exact same (Fin.ext vals)
        simp [member, same, Function.update_of_ne distinct]

/-- The source writer preserves each cell outside the destination region. -/
theorem storeSelectedLabels_outside (pointer : Word) (values : Fin 508 → Word)
    (indices : List (Fin 508)) (ram : Word → Word) (address : Word)
    (outside : ∀ index ∈ indices, address ≠ pointer + BitVec.ofNat 256 index.val) :
    storeSelectedLabels pointer values indices ram address = ram address := by
  induction indices generalizing ram with
  | nil => rfl
  | cons head tail ih =>
    change storeSelectedLabels pointer values tail
      (Function.update ram (pointer + BitVec.ofNat 256 head.val) (values head)) address = _
    rw [ih _ (fun index member => outside index (List.mem_cons_of_mem head member)),
      Function.update_of_ne (outside head (List.mem_cons_self))]

/-- The complete store has 7112 fixed instructions. -/
theorem selectedLabelStoreProgram_length : selectedLabelStoreProgram.length = 7112 := by
  have count (indices : List (Fin 508)) : (selectedLabelStores indices).length = 14 * indices.length := by
    induction indices with
    | nil => rfl
    | cons head tail ih =>
      simpa only [selectedLabelStores, List.flatMap_cons, List.length_append,
        selectedLabelStore_length, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        congrArg (fun n => 14 + n) ih
  rw [selectedLabelStoreProgram, count, List.length_finRange]

/-- The complete store gives the exact typed selected labels in RAM. -/
theorem selectedLabelStoreProgram_source [BN254.FieldCertificate]
    (coin : Security.SimulatorSampling.OfflineCoin) (input : BN254.AffineInput) (base : Memory)
    (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (disjoint : SelectedStoreDisjoint base) (index : Fin 508) :
    (executeLinear selectedLabelStoreProgram base).ram
      (base.registers 14 + BitVec.ofNat 256 index.val) =
      ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).get index).setWidth 256 := by
  have agreement : SelectedReadAgreement base base := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  rw [selectedLabelStoreProgram, (selectedLabelStores_memory base base agreement disjoint (List.finRange 508)).1,
    storeSelectedLabels_get]
  simp only [List.mem_finRange, ↓reduceIte]
  exact selectedLabelWord_source coin input base stored coordinates index

end Kriterion.ArgoMAC.ArithmeticSimulator
