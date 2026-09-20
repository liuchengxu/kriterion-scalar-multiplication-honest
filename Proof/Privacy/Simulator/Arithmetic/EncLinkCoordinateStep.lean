import Proof.Privacy.Simulator.Arithmetic.EncLinkCoordinate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- An internal row query retains the shifted active coordinate and the saved y coordinate. -/
theorem encLinkRowQuery_coordinate (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (fits : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index rest)).support) :
    before.ram 35 = memory.ram 35 >>> 1 ∧ before.ram 36 = memory.ram 36 := by
  have prepared := encLinkPrepared_family memory index rest state represented capacity
  have kept := internalForwardSamples_privateFrame attempts
    (state.permutations (encLinkPhysicalIndex index)).base.used
    (state.permutations (encLinkPhysicalIndex index)).overlay.length
    (encLinkPrepared memory index rest) before spent supported (encLinkPhysicalIndex index).castSucc
    (encLinkPrepared_values memory index rest).2.1
    (prepared.permutations (encLinkPhysicalIndex index)).base.count fits
  refine ⟨?_, ?_⟩
  · have same : before.ram 35 = (encLinkPrepared memory index rest).ram 35 := kept 35 (by decide) (by decide)
    rw [same, (encLinkPrepared_values memory index rest).2.2.2.1]
    simp
  · exact encLinkRowQuery_private attempts state memory before spent index rest represented capacity fits
      supported 36 (by decide) (by decide) (by decide)

/-- Every accepted row retains the exact next coordinate word. -/
theorem encLinkRowQuery_coordinateStep (attempts : Nat) (state : SparseOracleFamily)
    (memory before : Memory) (spent : Nat) (index : EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit)
    (supported : (before, spent) ∈ (internalForwardSamples attempts
      (state.permutations (encLinkPhysicalIndex index)).base.used
      (state.permutations (encLinkPhysicalIndex index)).overlay.length
      (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix))).support)
    (accepted : before.registers 7 ≠ 0#256) (x y : BitVec coordinateBitCount)
    (active : memory.ram 35 = encLinkCoordinateWord (indices.length + 1) x y)
    (saved : memory.ram 36 = y.setWidth 256) (count : indices.length + 1 ≤ 508) :
    (encLinkAfterQuery before).1.ram 35 = encLinkCoordinateWord indices.length x y ∧
    (encLinkAfterQuery before).1.ram 36 = y.setWidth 256 := by
  have room := encLinkInvariant_room state memory index indices suffix firstKey output limit ready
  have fit : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) ≤ 2 ^ 110 := by omega
  have kept := encLinkRowQuery_private attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  have cursor : before.ram 33 = BitVec.ofNat 256 output :=
    (kept 33 (by decide) (by decide) (by decide)).trans ready.cursor
  have upper : output < 2 ^ 96 := lt_of_le_of_lt (Nat.le_add_right _ _) ready.outputUpper
  have safe : ∀ scratch : Nat, scratch < 256 → before.ram 33 ≠ BitVec.ofNat 256 scratch := by
    intro scratch small
    rw [cursor]
    exact encLinkOutput_separate output scratch ready.outputLower upper small
  have transformed := encLinkAfterQuery_coordinate before accepted
    ⟨safe 32 (by decide), safe 35 (by decide), safe 36 (by decide), safe 38 (by decide)⟩
  have source := encLinkRowQuery_coordinate attempts state memory before spent index _
    ready.represented ready.capacity fit supported
  have counter : before.ram 38 = BitVec.ofNat 256 (indices.length + 1) :=
    (kept 38 (by decide) (by decide) (by decide)).trans ready.counter
  have boundary : BitVec.ofNat 256 indices.length = 254#256 ↔ indices.length = 254 := by
    constructor
    · intro equal
      have values := congrArg BitVec.toNat equal
      have bound : indices.length < 2 ^ 256 := by omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at values
      exact values
    · intro equal; rw [equal]
  refine ⟨?_, ?_⟩
  · rw [transformed.1, counter, BitVec.ofNat_add]
    simp only [show (1 : Word) = 1#256 from rfl, add_sub_cancel_right]
    rw [source.1, source.2, active, saved]
    simp only [boundary]
    simpa only [Nat.add_sub_cancel] using encLinkCoordinateWord_step (indices.length + 1) x y (by omega) count
  · exact transformed.2.trans (source.2.trans saved)

end Kriterion.ArgoMAC.ArithmeticSimulator
