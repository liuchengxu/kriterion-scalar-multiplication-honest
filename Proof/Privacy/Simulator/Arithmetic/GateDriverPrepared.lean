import Proof.Privacy.Simulator.Arithmetic.GateDriverPrefix

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography Cryptography.BoundedMachine

/-- The save block places each prepared range in its indexed scratch word. -/
theorem gateDirectiveSave_range (memory : Memory) (index : Fin 3) :
    (executeLinear gateDirectiveSave memory).ram (BitVec.ofNat 256 (17 + index.val)) =
      memory.registers ⟨4 + index.val, by omega⟩ := by
  have values := gateDirectiveSave_values memory
  fin_cases index
  · exact values.2.1
  · exact values.2.2.1
  · exact values.2.2.2.1

/-- The prepared false branch stores the exact three source hash commands. -/
theorem gateDriverPrepared_hash (gate : GateCode) (memory : Memory)
    (location : Pipeline.FixedKeyLocation) (label : Block) (target : BaseField) (quotient : HashLiftQuotient)
    (bit : gateDriverBit gate memory = false) (tweak : gate.tweak = location.tweak)
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.target) = BitVec.ofNat 256 target.val)
    (quotientWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.quotient) = BitVec.ofNat 256 quotient.val)
    (labelWord : memory.ram (memory.registers 14 + BitVec.ofNat 256 gate.selected.val) = label.setWidth 256) :
    (gateDriverPrepared gate memory).ram 16 = (gateInput location label).setWidth 256 ∧
    (gateDriverPrepared gate memory).ram 20 = 3 ∧
    ∀ index : Fin 3, (gateDriverPrepared gate memory).ram (BitVec.ofNat 256 (17 + index.val)) =
      (liftHashBlocks (goodHashLift target quotient).1 index ^^^ gateInput location label).setWidth 256 := by
  let loaded := executeLinear (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) memory
  have values := gateDirectiveLoad_values gate.selected gate.target gate.quotient gate.table memory
  have targetReady : loaded.registers 0 = BitVec.ofNat 256 target.val := values.1.trans targetWord
  have quotientReady : loaded.registers 1 = BitVec.ofNat 256 quotient.val := values.2.1.trans quotientWord
  have labelReady : loaded.registers 9 = label.setWidth 256 := values.2.2.2.1.trans labelWord
  have prepared : gateDriverPrepared gate memory = executeLinear gateDirectiveSave
      (executeLinear (gateHashProgram location.tweak) loaded) := by
    simp only [gateDriverPrepared, bit, tweak, gateBlocksMemory, Bool.false_eq_true, ↓reduceIte, loaded]
  rw [prepared]
  have saved := gateDirectiveSave_values (executeLinear (gateHashProgram location.tweak) loaded)
  refine ⟨saved.1.trans (gateHashProgram_input loaded location label labelReady),
    saved.2.2.2.2.1.trans (gateHashProgram_count location.tweak loaded), ?_⟩
  intro index
  rw [gateDirectiveSave_range]
  exact gateHashProgram_source loaded location label target quotient targetReady quotientReady labelReady index

/-- The prepared true branch stores the exact two source pad commands. -/
theorem gateDriverPrepared_pad (gate : GateCode) (memory : Memory)
    (location : Pipeline.FixedKeyLocation) (label : Block) (target : BaseField) (table : BitAdaptor.Table)
    (bit : gateDriverBit gate memory = true) (tweak : gate.tweak = location.tweak)
    (targetWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.target) = BitVec.ofNat 256 target.val)
    (tableWord : memory.ram (memory.registers 11 + BitVec.ofNat 256 gate.table) = table.trueRow)
    (labelWord : memory.ram (memory.registers 14 + BitVec.ofNat 256 gate.selected.val) = label.setWidth 256) :
    (gateDriverPrepared gate memory).ram 16 = (gateInput location label).setWidth 256 ∧
    (gateDriverPrepared gate memory).ram 20 = 2 ∧
    ∀ index : Fin 2, (gateDriverPrepared gate memory).ram (BitVec.ofNat 256 (17 + index.val)) =
      (targetPadBlocks table target index ^^^ gateInput location label).setWidth 256 := by
  let loaded := executeLinear (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) memory
  have values := gateDirectiveLoad_values gate.selected gate.target gate.quotient gate.table memory
  have targetReady : loaded.registers 0 = BitVec.ofNat 256 target.val := values.1.trans targetWord
  have tableReady : loaded.registers 8 = table.trueRow := values.2.2.1.trans tableWord
  have labelReady : loaded.registers 9 = label.setWidth 256 := values.2.2.2.1.trans labelWord
  have prepared : gateDriverPrepared gate memory = executeLinear gateDirectiveSave
      (executeLinear (gatePadProgram location.tweak) loaded) := by
    simp only [gateDriverPrepared, bit, tweak, gateBlocksMemory, ↓reduceIte, loaded]
  rw [prepared]
  have saved := gateDirectiveSave_values (executeLinear (gatePadProgram location.tweak) loaded)
  refine ⟨saved.1.trans (gatePadProgram_input loaded location label labelReady),
    saved.2.2.2.2.1.trans (gatePadProgram_count location.tweak loaded), ?_⟩
  intro index
  have stored := gateDirectiveSave_range (executeLinear (gatePadProgram location.tweak) loaded) index.castSucc
  exact stored.trans (gatePadProgram_source loaded location label target table targetReady tableReady labelReady index)

end Kriterion.ArgoMAC.ArithmeticSimulator
