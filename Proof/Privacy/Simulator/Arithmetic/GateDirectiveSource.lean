import Proof.Privacy.Simulator.Arithmetic.GateDirectiveLoad
import Proof.Privacy.Simulator.Arithmetic.GateQuotientLayout
import Proof.Privacy.Simulator.Arithmetic.GateBlocksMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography Cryptography.BoundedMachine Security.SimulatorSampling

/-- The loaded gate fields equal the typed private source. -/
theorem gateDirectiveLoad_data (coefficients gates : Nat) (data : GateData coefficients gates)
    (start : Nat) (gate : Fin gates) (index : Fin 254) (selected : Fin 508) (base : Memory)
    (stored : WordsAt base.ram (base.registers 11) start ((gateDataSchedule coefficients gates).words data)) :
    let result := executeLinear (gateDirectiveLoad selected
      (start + 254 * gate.val + index.val)
      (start + gates * 254 + 254 * gate.val + index.val)
      (start + 2 * gates * 254 + 254 * gate.val + index.val)) base
    result.registers 0 = BitVec.ofNat 256 (data.2.2.2 gate index).val ∧
    result.registers 1 = BitVec.ofNat 256 (data.2.2.1 gate index).val ∧
    result.registers 8 = ((data.2.1 gate).get index).trueRow := by
  have loaded := gateDirectiveLoad_values selected
    (start + 254 * gate.val + index.val)
    (start + gates * 254 + 254 * gate.val + index.val)
    (start + 2 * gates * 254 + 254 * gate.val + index.val) base
  exact ⟨loaded.1.trans (gateData_target coefficients gates data _ _ start gate index stored),
    loaded.2.1.trans (gateData_quotient coefficients gates data _ _ start gate index stored),
    loaded.2.2.1.trans (gateData_table coefficients gates data _ _ start gate index stored)⟩

/-- The false branch returns exactly three selected permutation ranges. -/
theorem gateHashProgram_count (tweak : Block) (base : Memory) :
    (executeLinear (gateHashProgram tweak) base).registers 7 = 3 := by
  rw [gateHashProgram, executeLinear_append]
  rfl

/-- The true branch returns exactly two selected permutation ranges. -/
theorem gatePadProgram_count (tweak : Block) (base : Memory) :
    (executeLinear (gatePadProgram tweak) base).registers 7 = 2 := by
  rw [gatePadProgram, executeLinear_append]
  rfl

/-- Both branches preserve RAM, stacks, and all caller pointers. -/
theorem gateBlocksMemory_preserves (tweak : Block) (bit : Bool) (base : Memory) :
    (gateBlocksMemory tweak bit base).ram = base.ram ∧
    (gateBlocksMemory tweak bit base).bits = base.bits ∧
    ∀ register : Register, 10 ≤ register.val →
      (gateBlocksMemory tweak bit base).registers register = base.registers register := by
  cases bit
  · exact gateHashProgram_preserves base tweak
  · exact gatePadProgram_preserves base tweak

/-- The selected branch retains the exact gate input. -/
theorem gateBlocksMemory_input (base : Memory) (location : Pipeline.FixedKeyLocation)
    (label : Block) (bit : Bool) (labelWord : base.registers 9 = label.setWidth 256) :
    (gateBlocksMemory location.tweak bit base).registers 9 = (gateInput location label).setWidth 256 := by
  cases bit
  · exact gateHashProgram_input base location label labelWord
  · exact gatePadProgram_input base location label labelWord

/-- The selected branch returns its exact active slot count. -/
theorem gateBlocksMemory_count (tweak : Block) (bit : Bool) (base : Memory) :
    (gateBlocksMemory tweak bit base).registers 7 = if bit then 2 else 3 := by
  cases bit
  · exact gateHashProgram_count tweak base
  · exact gatePadProgram_count tweak base

end Kriterion.ArgoMAC.ArithmeticSimulator
