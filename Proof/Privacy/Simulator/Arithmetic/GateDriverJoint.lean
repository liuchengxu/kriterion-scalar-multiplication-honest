import Proof.Privacy.Simulator.Arithmetic.GateSlotPrivate
import Proof.Privacy.Simulator.Arithmetic.GateDriverSource
import Proof.Privacy.Simulator.Arithmetic.CutoffMapBind

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

abbrev GateJointResult := (Fin 1036 × Memory × Nat) × SharedOracleSource

/-- The normal coupled return restores the saved caller pointers. -/
def gateRestoreCoupled (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  PMF.pure (some ((1034, executeLinear gateDirectiveRestore memory, 10), state))

/-- A successful slot continues with its exact instruction count. -/
def gateContinueCoupled (attempts : Nat) (gate : GateCode) (slot : Fin 3) (command : SharedCommand)
    (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  bindCutoff (gateDriverSlotCoupledSamples attempts gate slot memory state command) fun result =>
    (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2))

/-- The third coupled slot returns through the normal caller restoration. -/
def gateThirdCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 2 (commands 2) gateRestoreCoupled memory state

/-- The coupled test selects the same saved third-slot flag as the machine. -/
def gateTestCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  let tested := executeLinear gateDriverTest memory
  (if tested.registers 1 = 0 then gateThirdCoupled attempts gate commands tested state else gateRestoreCoupled tested state).map
    (Option.map fun result => ((result.1.1, result.1.2.1, 5 + result.1.2.2), result.2))

/-- The second coupled slot reaches the saved slot-count test. -/
def gateSecondCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 1 (commands 1) (gateTestCoupled attempts gate commands) memory state

/-- The coupled body executes both required slots and the optional third slot. -/
def gateBodyCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 0 (commands 0) (gateSecondCoupled attempts gate commands) memory state

/-- The complete joint driver charges its deterministic preparation instructions. -/
def gateDriverCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  (gateBodyCoupled attempts gate commands (gateDriverPrepared gate memory) state).map
    (Option.map fun result => ((result.1.1, result.1.2.1, gateDriverPrefixCost gate memory + result.1.2.2), result.2))

/-- The source marginal composes each successful slot with its typed continuation. -/
theorem gateContinueCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (command : SharedCommand) (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (target : SharedOracleSource → PMF (Option (Unit × SharedOracleSource)))
    (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (law : ∀ result updated, some ((), (result, updated)) ∈
      (gateDriverSlotCoupledSamples attempts gate slot memory state command).support →
      (next result.2.1 updated).map (Option.map fun tail => ((), tail.2)) = target updated) :
    (gateContinueCoupled attempts gate slot command next memory state).map (Option.map fun result => ((), result.2)) =
      bindCutoff (sharedSourceCutoff attempts (.inl (.program command)) state) (fun result => target result.2) := by
  unfold gateContinueCoupled
  have projected := cutoff_map_bind (gateDriverSlotCoupledSamples attempts gate slot memory state command)
    (fun result => (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2)))
    (fun result => (result.1, result.2.2)) (fun result => ((), result.2))
    (fun result => target result.2) (by
      rintro ⟨value, result, updated⟩ supported
      cases value
      simpa only [PMF.map_comp, Option.map_map, Function.comp_def] using law result updated supported)
  rw [projected]
  congr 1
  have base := represented.counts.1 (sharedPhysicalIndex (.inl command.1))
  exact gateDriverSlotCoupledSamples_source attempts gate slot memory state command represented.family represented.capacity
    stored.index stored.operand (by omega)

/-- The machine marginal composes each accepted slot with its actual continuation. -/
theorem gateContinueCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (command : SharedCommand) (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (target : Memory → PMF (Fin 1036 × Memory × Nat))
    (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (law : ∀ result updated, some ((), (result, updated)) ∈
      (gateDriverSlotCoupledSamples attempts gate slot memory state command).support →
      (next result.2.1 updated).map (Option.map Prod.fst) =
        (target result.2.1).map (fun tail => if tail.1 = 1035 then none else some tail)) :
    (gateContinueCoupled attempts gate slot command next memory state).map (Option.map Prod.fst) =
      ((gateDriverSlotSamples attempts gate slot memory).bind (gateDriverAfterSlot target)).map
        (fun result => if result.1 = 1035 then none else some result) := by
  let charged (result : Fin 305 × Memory × Nat) := (target result.2.1).map
    (fun tail => if tail.1 = 1035 then none else some (tail.1, tail.2.1, result.2.2 + tail.2.2))
  have projected := cutoff_map_bind (gateDriverSlotCoupledSamples attempts gate slot memory state command)
    (fun result => (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2)))
    (fun result => (result.1, result.2.1)) Prod.fst
    (fun result => charged result.2) (by
      rintro ⟨value, result, updated⟩ supported
      cases value
      have mapped := congrArg (PMF.map (Option.map fun tail : Fin 1036 × Memory × Nat =>
        (tail.1, tail.2.1, result.2.2 + tail.2.2))) (law result updated supported)
      simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
      rw [mapped]
      apply congrArg (fun f => PMF.map f (target result.2.1))
      funext tail
      split <;> rfl)
  change (bindCutoff _ _).map _ = _
  rw [projected, gateDriverSlotCoupledSamples_machine attempts gate slot memory state command represented.family
    represented.capacity represented.history stored.index stored.operand stored.target (represented.historyFits room)]
  simp only [bindCutoff, PMF.bind_map, PMF.map_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have labels := (gateDriverSlotSamples_cost attempts limit gate slot memory result attemptFits
    (gateDriverSlotReady_of_source attempts limit gate slot memory state command represented stored room) supported).2
  rcases labels with normal | failed
  · simp only [normal, show (300 : Fin 305) ≠ 304 by decide, ↓reduceIte, gateDriverAfterSlot, PMF.map_comp, Function.comp_def]
    rfl
  · simp only [failed, ↓reduceIte, gateDriverAfterSlot, show (304 : Fin 305) ≠ 300 by decide, PMF.pure_map, Function.comp_def]

end
end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine

set_option backward.isDefEq.respectTransparency false in
/-- The stored slot command selects the exact typed fresh-pair update. -/
theorem lazyGateSlot_oracle (gate : GateCode) (slot : Fin 3) (memory : Memory)
    (command : SharedCommand) (stored : GateCommandMemory gate slot memory command)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    (lazyGateSlot gate slot memory oracle).map Prod.snd =
      LazyOracle.program (.fixedForward command.1 command.2.1) command.2.2 oracle := by
  classical
  let ready := executeLinear (gateSlotLoad (gate.oracle slot) slot) memory
  have load := gateSlotLoad_values (gate.oracle slot) slot memory
  have input : ready.registers 8 = historyWord command.2.1 := load.1.trans stored.operand
  have index : ready.registers 9 =
      BitVec.ofNat 256 (Fintype.equivFin Shared.FixedKeyIndex command.1).val := by
    rw [load.2.1, stored.index, sharedPhysicalIndex_fixed]
  have target : ready.ram (14#256) = historyWord command.2.2 := by
    rw [load.2.2.2.1]
    change Function.update memory.ram 14 _ 14 = _
    rw [Function.update_self]
    exact stored.target
  have decodeBlock (block : Block) : BitVec.ofNat 128 (historyWord block).toNat = block := by
    have small : block.toNat < 2 ^ 256 := lt_trans block.isLt (by decide)
    change BitVec.ofNat 128 (block.toNat % 2 ^ 256) = block
    rw [Nat.mod_eq_of_lt small]
    exact BitVec.ofNat_toNat 128 block
  have small : (Fintype.equivFin Shared.FixedKeyIndex command.1).val < 2 ^ 256 :=
    lt_trans (Fintype.equivFin Shared.FixedKeyIndex command.1).isLt (by rw [sharedFixedKeyIndex_count]; decide)
  have decoded : queryFromRegisters (FixedIndex := Shared.FixedKeyIndex) (EncIndex := EncPRF.PermutationIndex)
      0 (ready.registers 9) (ready.registers 8) = some (.fixedForward command.1 command.2.1) := by
    rw [index, input]
    simp only [queryFromRegisters, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
    rw [dif_pos (Fintype.equivFin Shared.FixedKeyIndex command.1).isLt]
    change some (PublicQuery.fixedForward
      ((Fintype.equivFin Shared.FixedKeyIndex).symm (Fintype.equivFin Shared.FixedKeyIndex command.1))
      (BitVec.ofNat 128 (historyWord command.2.1).toNat)) = _
    rw [Equiv.symm_apply_apply, decodeBlock]
  unfold lazyGateSlot
  dsimp only
  rw [decoded]
  simp only [answerFromWords, Option.map_map, Function.comp_def]
  change Option.map id (LazyOracle.program (.fixedForward command.1 command.2.1)
    (BitVec.ofNat 128 (ready.ram (14#256)).toNat) oracle) = _
  rw [target, decodeBlock, Option.map_id]
  rfl

/-- A slot keeps every other stored command. -/
theorem GateCommandMemory.scratchEq {gate : GateCode} {slot : Fin 3} {memory updated : Memory}
    {command : SharedCommand} (stored : GateCommandMemory gate slot memory command)
    (same : ∀ address : Word, address ≠ 14 → updated.ram address = memory.ram address) :
    GateCommandMemory gate slot updated command := by
  refine ⟨stored.index, ?_, ?_⟩
  · rw [same 16 (by decide)]
    exact stored.operand
  · rw [same _ (by obtain ⟨slot, bounded⟩ := slot; interval_cases slot <;> simp only [Fin.val_mk] <;> decide)]
    exact stored.target

/-- A successful slot keeps each RAM cell outside its target scratch cell. -/
theorem lazyGateSlot_scratch {gate : GateCode} {slot : Fin 3} {memory result : Memory}
    {oracle updated : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex}
    (success : lazyGateSlot gate slot memory oracle = some (result, updated))
    (address : Word) (outside : address ≠ 14) : result.ram address = memory.ram address := by
  rw [(lazyGateSlot_memory gate slot memory result oracle updated success).1]
  exact Function.update_of_ne outside _ _

end Kriterion.ArgoMAC.ArithmeticSimulator
