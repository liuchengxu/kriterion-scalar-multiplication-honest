import Proof.Privacy.Simulator.Arithmetic.EncLinkRow

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Preparation changes only the selected label and coordinate scratch cells. -/
theorem encLinkPrepared_frame (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (cell : Word) (separate : cell ≠ 35 ∧ cell ≠ 41) :
    (encLinkPrepared memory index rest).ram cell = memory.ram cell := by
  rw [(encLinkPrepared_values memory index rest).2.2.2.1]
  simp only [Function.update_of_ne separate.1, Function.update_of_ne separate.2]

/-- Each internal row query preserves the saved caller data outside preparation writes. -/
theorem encLinkRowQuery_private (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (fits : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index rest)).support)
    (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96)
    (separate : cell ≠ 35 ∧ cell ≠ 41) :
    before.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have prepared := encLinkPrepared_family memory index rest state represented capacity
  have kept := internalForwardSamples_privateFrame attempts
    (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length
    (encLinkPrepared memory index rest) before spent supported (encLinkPhysicalIndex index).castSucc
    (encLinkPrepared_values memory index rest).2.1
    (prepared.permutations (encLinkPhysicalIndex index)).base.count fits cell lower upper
  rw [kept, encLinkPrepared_frame]
  constructor
  all_goals
    intro equal
    have values := congrArg BitVec.toNat equal
    have bound : cell < 2 ^ 256 := lt_trans upper (by decide)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at values
    simp only [show (35 : Word).toNat = 35 from rfl,
      show (41 : Word).toNat = 41 from rfl] at values
    omega

/-- Every row consumes its index bits and preserves the caller suffix. -/
theorem encLinkRowSamples_bits (attempts : Nat) (state : SparseOracleFamily)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) (input : Fin (2 ^ 128))
    (result : (Memory × Nat × Fin 7468) × SparseOracleFamily)
    (supported : result ∈ (encLinkRowSamples attempts state memory index rest input).support) :
    result.1.1.bits 0 = rest := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  change (encLinkAfterQuery before).1.bits 0 = rest
  rw [encLinkAfterQuery_bits, internalForwardSamples_bits _ _ _ _ before spent member]
  exact (encLinkPrepared_values memory index rest).2.2.2.2

/-- Every accepted row decreases the loop count and advances the label cursors. -/
theorem encLinkRowQuery_cursors (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (fits : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index rest)).support)
    (accepted : before.registers 7 ≠ 0#256)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (encLinkAfterQuery before).1.ram 32 = memory.ram 32 + 1 ∧
    (encLinkAfterQuery before).1.ram 33 = memory.ram 33 + 1 ∧
    (encLinkAfterQuery before).1.ram 38 = memory.ram 38 - 1 := by
  have kept := encLinkRowQuery_private attempts state memory before spent index rest
    represented capacity fits supported
  have a : before.ram 32 = memory.ram 32 := kept 32 (by decide) (by decide) (by decide)
  have b : before.ram 33 = memory.ram 33 := kept 33 (by decide) (by decide) (by decide)
  have c : before.ram 38 = memory.ram 38 := kept 38 (by decide) (by decide) (by decide)
  have first : before.ram 33#256 ≠ 32#256 := by change before.ram 33 ≠ (32 : Word); rw [b]; exact inputSafe
  have last : before.ram 33#256 ≠ 38#256 := by change before.ram 33 ≠ (38 : Word); rw [b]; exact countSafe
  simpa only [a, b, c] using encLinkAfterQuery_cursors before accepted first last

end Kriterion.ArgoMAC.ArithmeticSimulator
