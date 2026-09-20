import Construction.Simulator.PadBlocks
import Proof.Privacy.Simulator.Arithmetic.HashLiftSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Security Cryptography.BoundedMachine

/-- The fixed mask returns the exact widened low block. -/
theorem wordLowBlock (value : Word) :
    Arithmetic.and.eval value (BitVec.ofNat 256 (2 ^ 128 - 1)) = (value.extractLsb' 0 128).setWidth 256 := by
  have same : BitVec.ofNat 256 value.toNat = value := by simp
  conv_lhs => rw [← same, wordMask128_nat]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

/-- The fixed shift returns the exact widened high block. -/
theorem wordHighBlock (value : Word) :
    Arithmetic.shiftRight.eval value 128 = (value.extractLsb' 128 128).setWidth 256 := by
  have bound : value.toNat / 2 ^ 128 < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
    simpa only [show 2 ^ 128 * 2 ^ 128 = 2 ^ 256 by norm_num] using value.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Arithmetic.eval, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change value.toNat / 2 ^ 128 = (value.toNat / 2 ^ 128 % 2 ^ 128) % 2 ^ 256
  rw [Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt (lt_trans bound (by decide : 2 ^ 128 < 2 ^ 256))]

/-- The pad program returns the exact original encrypted-target blocks. -/
theorem padBlocksProgram_source (base : Memory) (table : BitAdaptor.Table) (target : BaseField)
    (targetWord : base.registers 0 = BitVec.ofNat 256 target.val)
    (tableWord : base.registers 8 = table.trueRow) (index : Fin 2) :
    (executeLinear padBlocksProgram base).registers ⟨4 + index.val, by omega⟩ =
      (targetPadBlocks table target index).setWidth 256 := by
  fin_cases index <;>
    simp only [padBlocksProgram, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
      Function.update_apply, Fin.reduceEq, ↓reduceIte, targetWord, tableWord]
  · exact wordLowBlock (table.trueRow ^^^ BitVec.ofNat 256 target.val)
  · exact wordHighBlock (table.trueRow ^^^ BitVec.ofNat 256 target.val)

/-- The pad program preserves RAM, stacks, and all caller registers. -/
theorem padBlocksProgram_preserves (base : Memory) :
    (executeLinear padBlocksProgram base).ram = base.ram ∧
    (executeLinear padBlocksProgram base).bits = base.bits ∧
    ∀ register : Register, 9 ≤ register.val → (executeLinear padBlocksProgram base).registers register = base.registers register := by
  refine ⟨rfl, rfl, ?_⟩
  intro register caller
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [padBlocksProgram, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute,
    Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 3 (by decide)),
    Function.update_of_ne (different 4 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 8 (by decide))]

/-- The pad program charges five fixed instructions. -/
theorem padBlocksProgram_length : padBlocksProgram.length = 5 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
