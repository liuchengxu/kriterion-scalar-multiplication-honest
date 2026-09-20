import Proof.Privacy.Simulator.Arithmetic.EncLinkProgress

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Preparation stores the exact selected input label for its oracle call. -/
theorem encLinkPrepared_selected (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) :
    (encLinkPrepared memory index rest).ram 41 = memory.ram (memory.ram 32) := by
  rw [(encLinkPrepared_values memory index rest).2.2.2.1]
  simp

/-- An internal query retains the prepared selected label and both whitening keys. -/
theorem encLinkRowQuery_selected (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (fits : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index rest)).support) :
    before.ram 41 = memory.ram (memory.ram 32) ∧ before.ram 40 = memory.ram 40 := by
  have prepared := encLinkPrepared_family memory index rest state represented capacity
  have kept := internalForwardSamples_privateFrame attempts
    (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length
    (encLinkPrepared memory index rest) before spent supported (encLinkPhysicalIndex index).castSucc
    (encLinkPrepared_values memory index rest).2.1
    (prepared.permutations (encLinkPhysicalIndex index)).base.count fits
  refine ⟨?_, ?_⟩
  · have same : before.ram 41 = (encLinkPrepared memory index rest).ram 41 := kept 41 (by decide) (by decide)
    exact same.trans (encLinkPrepared_selected memory index rest)
  · exact encLinkRowQuery_private attempts state memory before spent index rest represented capacity fits
      supported 40 (by decide) (by decide) (by decide)

/-- The accepted machine row writes the exact selected source transform. -/
theorem encLinkRowQuery_output (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (accepted : before.registers 7 ≠ 0#256) (secondKey label : Block)
    (key : memory.ram 40 = secondKey.setWidth 256)
    (selected : memory.ram (memory.ram 32) = label.setWidth 256) :
    (encLinkAfterQuery before).1.ram (BitVec.ofNat 256 output) =
      (before.registers 8 ^^^ secondKey.setWidth 256) ^^^ label.setWidth 256 := by
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have kept := encLinkRowQuery_private attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output :=
    (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have separate : ∀ scratch : Nat, scratch < 256 → before.ram 33 ≠ BitVec.ofNat 256 scratch := by
    intro scratch small
    rw [cursor]
    exact encLinkOutput_separate output scratch ready.outputLower upper small
  have data := encLinkRowQuery_selected attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  rw [← cursor, encLinkAfterQuery_output before accepted
    ⟨separate 32 (by decide), separate 33 (by decide), separate 35 (by decide), separate 38 (by decide)⟩,
    data.1, data.2, key, selected]

end Kriterion.ArgoMAC.ArithmeticSimulator
