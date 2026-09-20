import Construction.Simulator.GateBlocks
import Proof.Privacy.Simulator.Arithmetic.HashLiftSource
import Proof.Privacy.Simulator.Arithmetic.PadBlocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The gate tweak matches the source's 128-bit exclusive-or input. -/
theorem gateTweakProgram_source (base : Memory) (label tweak : Block)
    (encoded : base.registers 9 = label.setWidth 256) :
    (executeLinear (gateTweakProgram tweak) base).registers 9 = (label ^^^ tweak).setWidth 256 := by
  simp [gateTweakProgram, executeLinear, LinearInstruction.execute, Arithmetic.eval, encoded, BitVec.setWidth_xor]

/-- The gate tweak preserves RAM, stacks, and every register outside two and nine. -/
theorem gateTweakProgram_preserves (base : Memory) (tweak : Block) :
    (executeLinear (gateTweakProgram tweak) base).ram = base.ram ∧
    (executeLinear (gateTweakProgram tweak) base).bits = base.bits ∧
    ∀ register : Register, register ≠ 2 → register ≠ 9 →
      (executeLinear (gateTweakProgram tweak) base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register notTwo notNine
  simp [gateTweakProgram, executeLinear, LinearInstruction.execute, notTwo, notNine]

/-- The hash range block applies the common input mask to each hash block. -/
theorem gateHashRanges_source (base : Memory) (index : Fin 3) :
    (executeLinear gateHashRanges base).registers ⟨4 + index.val, by omega⟩ =
      base.registers ⟨4 + index.val, by omega⟩ ^^^ base.registers 9 := by
  fin_cases index <;> simp [gateHashRanges, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The pad range block applies the common input mask to each pad block. -/
theorem gatePadRanges_source (base : Memory) (index : Fin 2) :
    (executeLinear gatePadRanges base).registers ⟨4 + index.val, by omega⟩ =
      base.registers ⟨4 + index.val, by omega⟩ ^^^ base.registers 9 := by
  fin_cases index <;> simp [gatePadRanges, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The hash range block preserves all source data and caller registers. -/
theorem gateHashRanges_preserves (base : Memory) :
    (executeLinear gateHashRanges base).ram = base.ram ∧
    (executeLinear gateHashRanges base).bits = base.bits ∧
    ∀ register : Register, 8 ≤ register.val → (executeLinear gateHashRanges base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 8) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gateHashRanges, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 4 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 7 (by decide))]

/-- The pad range block preserves all source data and caller registers. -/
theorem gatePadRanges_preserves (base : Memory) :
    (executeLinear gatePadRanges base).ram = base.ram ∧
    (executeLinear gatePadRanges base).bits = base.bits ∧
    ∀ register : Register, 8 ≤ register.val → (executeLinear gatePadRanges base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 8) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [gatePadRanges, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 4 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 7 (by decide))]

end Kriterion.ArgoMAC.ArithmeticSimulator
