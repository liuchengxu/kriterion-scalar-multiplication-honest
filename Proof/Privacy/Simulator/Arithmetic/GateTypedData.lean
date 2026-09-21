import Proof.Privacy.Simulator.Arithmetic.GateLoopInitialReady
import Proof.Privacy.Simulator.Arithmetic.SharedGateDirectiveCommands

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- These fields connect one descriptor to its exact typed directive. -/
structure GateTypedData (memory : Memory) (gate : GateCode) (directive : GateDirective) (quotient : HashLiftQuotient) : Prop where
  bit : gateDriverBit gate memory = directive.bit
  tweak : gate.tweak = directive.location.tweak
  indices : ∀ slot, gate.oracle slot =
    (sharedPhysicalIndex (.inl (Shared.fixedIndex (fixedKeyIndex directive.location directive.window (.hash slot))))).val
  target : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.target) = BitVec.ofNat 256 directive.target.val
  quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.quotient) = BitVec.ofNat 256 quotient.val
  table : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.table) = directive.table.trueRow
  label : memory.ram (memory.registers 14 + BitVec.ofNat 256 gate.selected.val) = directive.label.setWidth 256
  lift : directive.lift = goodHashLift directive.target quotient

/-- Every word read by a descriptor lies in the preserved private region. -/
structure GatePrivateAddresses (memory : Memory) (gate : GateCode) : Prop where
  source : ∀ offset ∈ [gate.target, gate.quotient, gate.table],
    32 ≤ (memory.registers 11 + BitVec.ofNat 256 offset).toNat ∧
    (memory.registers 11 + BitVec.ofNat 256 offset).toNat < 2 ^ 96
  coordinate : 32 ≤ (memory.registers 12 + BitVec.ofNat 256 (selectedCoordinate gate.selected)).toNat ∧
    (memory.registers 12 + BitVec.ofNat 256 (selectedCoordinate gate.selected)).toNat < 2 ^ 96
  label : 32 ≤ (memory.registers 14 + BitVec.ofNat 256 gate.selected.val).toNat ∧
    (memory.registers 14 + BitVec.ofNat 256 gate.selected.val).toNat < 2 ^ 96

/-- The private relation preserves a word in its original machine representation. -/
theorem GatePrivateAgreement.word {memory initial : Memory} (agreement : GatePrivateAgreement memory initial)
    (address : Word) (lower : 32 ≤ address.toNat) (upper : address.toNat < 2 ^ 96) :
    memory.ram address = initial.ram address := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using agreement.words address.toNat lower upper

/-- Preserved pointers and private words retain every typed descriptor field. -/
theorem GateTypedData.ofAgreement {memory initial : Memory} (agreement : GatePrivateAgreement memory initial)
    (gate : GateCode) (directive : GateDirective) (quotient : HashLiftQuotient)
    (data : GateTypedData initial gate directive quotient) (bounds : GatePrivateAddresses initial gate) :
    GateTypedData memory gate directive quotient := by
  have source (offset : Nat) (member : offset ∈ [gate.target, gate.quotient, gate.table]) :
      memory.ram (memory.registers 11 + BitVec.ofNat 256 offset) = initial.ram (initial.registers 11 + BitVec.ofNat 256 offset) := by
    rw [agreement.source]
    exact agreement.word _ (bounds.source offset member).1 (bounds.source offset member).2
  refine ⟨?_, data.tweak, data.indices, (source _ (by simp)).trans data.target,
    (source _ (by simp)).trans data.quotientWord, (source _ (by simp)).trans data.table, ?_, data.lift⟩
  · unfold gateDriverBit
    rw [agreement.input, agreement.word _ bounds.coordinate.1 bounds.coordinate.2]
    exact data.bit
  · rw [agreement.labels, agreement.word _ bounds.label.1 bounds.label.2]
    exact data.label

/-- Typed initial descriptors establish every reached command in the complete loop. -/
theorem gateLoopCoupledReady_typed [BN254.FieldCertificate] {count : Nat}
    (plan : Vector GateCode count) (directives : Fin count → GateDirective) (quotients : Fin count → HashLiftQuotient)
    (attempts remaining index limit : Nat) (memory initial : Memory) (state : SharedOracleSource)
    (inside : index + remaining ≤ count) (agreement : GatePrivateAgreement memory initial)
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110)
    (data : ∀ gate : Fin count, GateTypedData initial plan[gate.val] (directives gate) (quotients gate))
    (bounds : ∀ gate : Fin count, GatePrivateAddresses initial plan[gate.val]) :
    GateLoopCoupledReady plan (fun gate => sharedDirectiveSlot (directives gate)) (fun gate => !(directives gate).bit)
      attempts remaining index limit memory state := by
  apply gateLoopCoupledReady_of_initial _ _ _ _ _ _ _ memory initial state inside agreement represented room
  intro current frame gate
  have exactData := GateTypedData.ofAgreement frame plan[gate.val] (directives gate) (quotients gate) (data gate) (bounds gate)
  exact sharedDirectiveSlot_prepared _ current (directives gate) (quotients gate) exactData.bit exactData.tweak
    exactData.indices exactData.target exactData.quotientWord exactData.table exactData.label exactData.lift

/-- A typed strict gate programs exactly its source directive. -/
theorem lazyGateDriverResult_directive (gate : GateCode) (memory : Memory)
    (directive : GateDirective) (quotient : HashLiftQuotient)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (data : GateTypedData memory gate directive quotient) :
    (lazyGateDriverResult gate memory oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle (directive.commands.map sharedCommand) := by
  have prepared := sharedDirectiveSlot_prepared gate memory directive quotient data.bit data.tweak
    data.indices data.target data.quotientWord data.table data.label data.lift
  rw [← sharedDirectiveSlot_list]
  exact lazyGateDriverResult_oracle gate memory (sharedDirectiveSlot directive) (!directive.bit)
    oracle prepared.2 prepared.1

/-- The strict loop follows the exact ordered source commands. -/
theorem lazyGateLoopResults_source {count : Nat} (plan : Vector GateCode count)
    (directives : Fin count → GateDirective) (quotients : Fin count → HashLiftQuotient)
    (remaining index : Nat) (memory initial : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (inside : index + remaining ≤ count) (agreement : GatePrivateAgreement memory initial)
    (data : ∀ gate : Fin count, GateTypedData initial plan[gate.val] (directives gate) (quotients gate))
    (bounds : ∀ gate : Fin count, GatePrivateAddresses initial plan[gate.val]) :
    (lazyGateLoopResults plan remaining index memory oracle).map (fun result => result.2.1) =
      OperationalOracle.strictCommands oracle
        (gateLoopCommandList (fun gate => sharedDirectiveSlot (directives gate))
          (fun gate => !(directives gate).bit) remaining index) := by
  induction remaining generalizing index memory oracle with
  | zero => simp [lazyGateLoopResults, gateLoopCommandList, OperationalOracle.strictCommands]
  | succ remaining ih =>
    have here : index < count := by omega
    let selected : Fin count := ⟨index, here⟩
    have typed := GateTypedData.ofAgreement agreement plan[index] (directives selected)
      (quotients selected) (data selected) (bounds selected)
    have prepared := sharedDirectiveSlot_prepared plan[index] memory (directives selected)
      (quotients selected) typed.bit typed.tweak typed.indices typed.target typed.quotientWord
      typed.table typed.label typed.lift
    have source := lazyGateDriverResult_oracle plan[index] memory
      (sharedDirectiveSlot (directives selected)) (!(directives selected).bit) oracle prepared.2 prepared.1
    simp only [lazyGateLoopResults, gateLoopCommandList, dif_pos here, OperationalOracle.strictCommands_append]
    dsimp only [Bind.bind]
    cases reached : lazyGateDriverResult plan[index] memory oracle with
    | none =>
      have failed : OperationalOracle.strictCommands oracle
          (sharedGateCommandList (sharedDirectiveSlot (directives selected)) (!(directives selected).bit)) = none := by
        simpa [reached] using source.symm
      simp [failed, selected]
    | some head =>
      have successful : OperationalOracle.strictCommands oracle
          (sharedGateCommandList (sharedDirectiveSlot (directives selected)) (!(directives selected).bit)) = some head.2.1 := by
        simpa [reached] using source.symm
      simp only [Option.bind_some, Option.map_bind, Option.map_some, Function.comp_def]
      rw [show OperationalOracle.strictCommands oracle
        (sharedGateCommandList (sharedDirectiveSlot (directives ⟨index, here⟩)) (!(directives ⟨index, here⟩).bit)) = some head.2.1 from successful]
      simp only [Option.bind_some]
      change (lazyGateLoopResults plan remaining (index + 1) head.1 head.2.1).bind
        (some ∘ (fun result => result.2.1)) = _
      rw [← Option.map_eq_bind]
      exact ih (index + 1) head.1 head.2.1 (by omega)
        (GatePrivateAgreement.afterLazyGate plan[index] memory initial oracle agreement head reached) data bounds

theorem GatePrivateAgreement.afterLazyLoop {count : Nat} (plan : Vector GateCode count)
    (remaining index : Nat) (memory initial : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (agreement : GatePrivateAgreement memory initial) (result)
    (success : lazyGateLoopResults plan remaining index memory oracle = some result) :
    GatePrivateAgreement result.1 initial := by
  induction remaining generalizing index memory oracle result with
  | zero =>
    simp only [lazyGateLoopResults, Option.some.injEq] at success
    subst result
    exact agreement
  | succ remaining ih =>
    unfold lazyGateLoopResults at success
    split at success
    · rename_i inside
      dsimp only [Bind.bind] at success
      obtain ⟨head, reached, tail, tailReached, equal⟩ :=
        (by simpa only [Option.bind_eq_some_iff] using success)
      cases equal
      exact ih (index + 1) head.1 head.2.1
        (GatePrivateAgreement.afterLazyGate plan[index] memory initial oracle agreement head reached)
        tail tailReached
    · contradiction


end
end Kriterion.ArgoMAC.ArithmeticSimulator
