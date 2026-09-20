import Proof.Privacy.Simulator.Arithmetic.SharedCommandListProgram
import Proof.Privacy.Simulator.Arithmetic.GateDriverPrepared
import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- Each directive uses the same three physical slots for its hash and pad branches. -/
def sharedDirectiveSlot (directive : GateDirective) (slot : Fin 3) : SharedCommand :=
  (Shared.fixedIndex (fixedKeyIndex directive.location directive.window (.hash slot)),
    gateInput directive.location directive.label,
    (if directive.bit then targetPadBlocks directive.table directive.target ⟨slot.val % 2, Nat.mod_lt _ (by decide)⟩
      else liftHashBlocks directive.lift.1 slot) ^^^ gateInput directive.location directive.label)

/-- The physical slot list is the exact shared image of the source directive's command list. -/
theorem sharedDirectiveSlot_list (directive : GateDirective) :
    sharedGateCommandList (sharedDirectiveSlot directive) (!directive.bit) = directive.commands.map sharedCommand := by
  cases bit : directive.bit <;>
    simp [sharedGateCommandList, sharedDirectiveSlot, GateDirective.commands, GateDirective.programRecords,
      fixedProgramRecord, sharedCommand, Shared.fixedIndex, fixedKeyIndex, Shared.slotIndex, bit]

private theorem historyWord_width (block : Block) : historyWord block = block.setWidth 256 := by
  apply BitVec.eq_of_toNat_eq
  simp only [historyWord, BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- Gate preparation stores exactly the active source commands and the correct slot count. -/
theorem sharedDirectiveSlot_prepared (gate : GateCode) (memory : Memory) (directive : GateDirective)
    (quotient : HashLiftQuotient)
    (bit : gateDriverBit gate memory = directive.bit) (tweak : gate.tweak = directive.location.tweak)
    (indices : ∀ slot, gate.oracle slot =
      (sharedPhysicalIndex (.inl (Shared.fixedIndex (fixedKeyIndex directive.location directive.window (.hash slot))))).val)
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.target) = BitVec.ofNat 256 directive.target.val)
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.quotient) = BitVec.ofNat 256 quotient.val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.table) = directive.table.trueRow)
    (labelWord : memory.ram (memory.registers 14 + BitVec.ofNat 256 gate.selected.val) = directive.label.setWidth 256)
    (lift : directive.lift = goodHashLift directive.target quotient) :
    (gateDriverPrepared gate memory).ram 20 = (if !directive.bit then 3 else 2) ∧
    ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (sharedDirectiveSlot directive slot) := by
  cases selected : directive.bit with
  | false =>
    have prepared := gateDriverPrepared_hash gate memory directive.location directive.label directive.target quotient
      (bit.trans selected) tweak targetWord quotientWord labelWord
    refine ⟨by simpa only [selected, Bool.not_false, ↓reduceIte] using prepared.2.1, ?_⟩
    intro slot _
    refine ⟨indices slot, by simpa only [sharedDirectiveSlot, historyWord_width] using prepared.1, ?_⟩
    simpa only [sharedDirectiveSlot, historyWord_width, selected, Bool.false_eq_true, ↓reduceIte, lift] using prepared.2.2 slot
  | true =>
    have prepared := gateDriverPrepared_pad gate memory directive.location directive.label directive.target directive.table
      (bit.trans selected) tweak targetWord tableWord labelWord
    refine ⟨by simpa only [selected, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using prepared.2.1, ?_⟩
    intro slot active
    have inside : slot.val < 2 := active.elim id (fun impossible => by rw [prepared.2.1] at impossible; contradiction)
    refine ⟨indices slot, by simpa only [sharedDirectiveSlot, historyWord_width] using prepared.1, ?_⟩
    simpa only [sharedDirectiveSlot, historyWord_width, selected, ↓reduceIte, Nat.mod_eq_of_lt inside] using prepared.2.2 ⟨slot.val, inside⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
