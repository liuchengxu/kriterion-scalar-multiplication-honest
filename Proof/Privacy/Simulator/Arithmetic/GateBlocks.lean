import Proof.Privacy.Simulator.Arithmetic.GateBlockRanges
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography Cryptography.BoundedMachine

/-- The false-branch program returns the exact selected hash permutation ranges. -/
theorem gateHashProgram_source (base : Memory) (location : Pipeline.FixedKeyLocation)
    (label : Block) (target : BaseField) (quotient : HashLiftQuotient)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (quotientWord : base.registers 1 = BitVec.ofNat 256 quotient.val)
    (labelWord : base.registers 9 = label.setWidth 256) (index : Fin 3) :
    (executeLinear (gateHashProgram location.tweak) base).registers ⟨4 + index.val, by omega⟩ =
      (liftHashBlocks (goodHashLift target quotient).1 index ^^^ gateInput location label).setWidth 256 := by
  have saved := gateTweakProgram_preserves base location.tweak
  have targetReady := (saved.2.2 0 (by decide) (by decide)).trans targetWord
  have quotientReady := (saved.2.2 1 (by decide) (by decide)).trans quotientWord
  rw [gateHashProgram, executeLinear_append, executeLinear_append, gateHashRanges_source,
    hashLiftProgram_source _ target quotient targetReady quotientReady,
    (hashLiftProgram_preserves _).2.2 9 (by decide), gateTweakProgram_source base label location.tweak labelWord]
  exact BitVec.setWidth_xor.symm

/-- The true-branch program returns the exact selected pad permutation ranges. -/
theorem gatePadProgram_source (base : Memory) (location : Pipeline.FixedKeyLocation)
    (label : Block) (target : BaseField) (table : BitAdaptor.Table)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (tableWord : base.registers 8 = table.trueRow)
    (labelWord : base.registers 9 = label.setWidth 256) (index : Fin 2) :
    (executeLinear (gatePadProgram location.tweak) base).registers ⟨4 + index.val, by omega⟩ =
      (targetPadBlocks table target index ^^^ gateInput location label).setWidth 256 := by
  have saved := gateTweakProgram_preserves base location.tweak
  have targetReady := (saved.2.2 0 (by decide) (by decide)).trans targetWord
  have tableReady := (saved.2.2 8 (by decide) (by decide)).trans tableWord
  rw [gatePadProgram, executeLinear_append, executeLinear_append, gatePadRanges_source,
    padBlocksProgram_source _ table target targetReady tableReady,
    (padBlocksProgram_preserves _).2.2 9 (by decide), gateTweakProgram_source base label location.tweak labelWord]
  exact BitVec.setWidth_xor.symm

/-- The hash branch retains the exact permutation input in register nine. -/
theorem gateHashProgram_input (base : Memory) (location : Pipeline.FixedKeyLocation) (label : Block)
    (labelWord : base.registers 9 = label.setWidth 256) :
    (executeLinear (gateHashProgram location.tweak) base).registers 9 = (gateInput location label).setWidth 256 := by
  rw [gateHashProgram, executeLinear_append, executeLinear_append,
    (gateHashRanges_preserves _).2.2 9 (by decide), (hashLiftProgram_preserves _).2.2 9 (by decide)]
  exact gateTweakProgram_source base label location.tweak labelWord

/-- The pad branch retains the exact permutation input in register nine. -/
theorem gatePadProgram_input (base : Memory) (location : Pipeline.FixedKeyLocation) (label : Block)
    (labelWord : base.registers 9 = label.setWidth 256) :
    (executeLinear (gatePadProgram location.tweak) base).registers 9 = (gateInput location label).setWidth 256 := by
  rw [gatePadProgram, executeLinear_append, executeLinear_append,
    (gatePadRanges_preserves _).2.2 9 (by decide), (padBlocksProgram_preserves _).2.2 9 (by decide)]
  exact gateTweakProgram_source base label location.tweak labelWord

/-- The hash branch preserves RAM, stacks, and registers ten through fifteen. -/
theorem gateHashProgram_preserves (base : Memory) (tweak : Block) :
    (executeLinear (gateHashProgram tweak) base).ram = base.ram ∧
    (executeLinear (gateHashProgram tweak) base).bits = base.bits ∧
    ∀ register : Register, 10 ≤ register.val → (executeLinear (gateHashProgram tweak) base).registers register = base.registers register := by
  rw [gateHashProgram, executeLinear_append, executeLinear_append]
  have first := gateTweakProgram_preserves base tweak
  have second := hashLiftProgram_preserves (executeLinear (gateTweakProgram tweak) base)
  have third := gateHashRanges_preserves (executeLinear hashLiftProgram (executeLinear (gateTweakProgram tweak) base))
  refine ⟨third.1.trans (second.1.trans first.1), third.2.1.trans (second.2.1.trans first.2.1), ?_⟩
  intro register caller
  have notTwo : register ≠ 2 := by intro same; have value := congrArg Fin.val same; omega
  have notNine : register ≠ 9 := by intro same; have value := congrArg Fin.val same; omega
  exact (third.2.2 register (by omega)).trans ((second.2.2 register (by omega)).trans (first.2.2 register notTwo notNine))

/-- The pad branch preserves RAM, stacks, and registers ten through fifteen. -/
theorem gatePadProgram_preserves (base : Memory) (tweak : Block) :
    (executeLinear (gatePadProgram tweak) base).ram = base.ram ∧
    (executeLinear (gatePadProgram tweak) base).bits = base.bits ∧
    ∀ register : Register, 10 ≤ register.val → (executeLinear (gatePadProgram tweak) base).registers register = base.registers register := by
  rw [gatePadProgram, executeLinear_append, executeLinear_append]
  have first := gateTweakProgram_preserves base tweak
  have second := padBlocksProgram_preserves (executeLinear (gateTweakProgram tweak) base)
  have third := gatePadRanges_preserves (executeLinear padBlocksProgram (executeLinear (gateTweakProgram tweak) base))
  refine ⟨third.1.trans (second.1.trans first.1), third.2.1.trans (second.2.1.trans first.2.1), ?_⟩
  intro register caller
  have notTwo : register ≠ 2 := by intro same; have value := congrArg Fin.val same; omega
  have notNine : register ≠ 9 := by intro same; have value := congrArg Fin.val same; omega
  exact (third.2.2 register (by omega)).trans ((second.2.2 register (by omega)).trans (first.2.2 register notTwo notNine))

/-- The false branch charges its full hash-lift and range computation. -/
theorem gateHashProgram_length (tweak : Block) : (gateHashProgram tweak).length = 27 := by
  simp [gateHashProgram, gateTweakProgram, hashLiftProgram_length, gateHashRanges]

/-- The true branch charges its full pad and range computation. -/
theorem gatePadProgram_length (tweak : Block) : (gatePadProgram tweak).length = 10 := by
  simp [gatePadProgram, gateTweakProgram, padBlocksProgram_length, gatePadRanges]

end Kriterion.ArgoMAC.ArithmeticSimulator
