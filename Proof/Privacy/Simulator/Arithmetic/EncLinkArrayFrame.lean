import Proof.Privacy.Simulator.Arithmetic.EncLinkSelected
import Proof.Privacy.Simulator.Arithmetic.WordsAt

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- A complete link row preserves each private word outside its current output cell. -/
theorem encLinkRowQuery_frameNat (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (cell : Nat) (lower : 256 ≤ cell) (upper : cell < 2 ^ 96) (outside : cell ≠ output) :
    (encLinkAfterQuery before).1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have kept := encLinkRowQuery_private attempts state memory before spent index _ ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output := (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have outputUpper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have separate (scratch : Nat) (small : scratch < 256) : before.ram 33 ≠ BitVec.ofNat 256 scratch := by
    rw [cursor]
    exact encLinkOutput_separate output scratch ready.outputLower outputUpper small
  have cellSeparate (scratch : Nat) (small : scratch < 256) : BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch :=
    encLinkOutput_separate cell scratch lower upper small
  have outputSeparate : BitVec.ofNat 256 cell ≠ before.ram 33 := by
    rw [cursor]
    intro same
    have values := congrArg BitVec.toNat same
    have cellFits : cell < 2 ^ 256 := lt_trans upper (by decide)
    have outputFits : output < 2 ^ 256 := lt_trans outputUpper (by decide)
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cellFits, Nat.mod_eq_of_lt outputFits] at values
    exact outside values
  rw [encLinkAfterQuery_frame before _ (separate 32 (by decide)) (separate 38 (by decide)) outputSeparate
    ⟨cellSeparate 32 (by decide), cellSeparate 33 (by decide), cellSeparate 35 (by decide), cellSeparate 38 (by decide)⟩]
  exact kept cell (by omega) upper ⟨by omega, by omega⟩

/-- A complete link row preserves any private array that excludes its current output cell. -/
theorem encLinkRowQuery_wordsAt (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (base start : Nat) (words : List Word) (lower : 256 ≤ base + start)
    (upper : base + start + words.length ≤ 2 ^ 96)
    (separate : ∀ position, position < words.length → base + start + position ≠ output)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 base) start words) :
    WordsAt (encLinkAfterQuery before).1.ram (BitVec.ofNat 256 base) start words := by
  intro position inside
  have kept := encLinkRowQuery_frameNat attempts state memory before spent index indices suffix firstKey output limit
    ready supported (base + start + position) (by omega) (by omega) (separate position inside)
  have encoded := stored position inside
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using kept.trans (by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using encoded)

/-- An exact next output word extends the established output prefix. -/
theorem wordsAt_append_last {ram : Word → Word} {pointer : Word} {start : Nat} {words : List Word} {value : Word}
    (stored : WordsAt ram pointer start words)
    (last : ram (pointer + BitVec.ofNat 256 (start + words.length)) = value) :
    WordsAt ram pointer start (words ++ [value]) := by
  intro position inside
  by_cases earlier : position < words.length
  · simpa only [List.getElem_append_left earlier] using stored position earlier
  · have final : position = words.length := by simp only [List.length_append, List.length_singleton] at inside; omega
    subst position
    simpa using last

end Kriterion.ArgoMAC.ArithmeticSimulator
