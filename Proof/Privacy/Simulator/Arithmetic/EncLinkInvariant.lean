import Proof.Privacy.Simulator.Arithmetic.EncLinkRowState
import Proof.Privacy.Simulator.Arithmetic.EncLinkTransform

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The loop invariant retains the physical state and the remaining fixed schedule. -/
structure EncLinkLoopMemory (state : SparseOracleFamily) (memory : Memory)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat) : Prop where
  represented : OracleFamilyMemory memory.ram state
  capacity : OracleFamilyFits state
  baseCount : ∀ index, (state.permutations index).base.used ≤ limit
  overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit
  room : 2 * (limit + indices.length) + 256 < 2 ^ 110
  counter : memory.ram 38 = BitVec.ofNat 256 indices.length
  cursor : memory.ram 33 = BitVec.ofNat 256 output
  outputLower : 256 ≤ output
  outputUpper : output + indices.length < 2 ^ 96
  whitening : memory.ram 39 = firstKey.setWidth 256
  wire : memory.bits 0 = indices.flatMap encLinkIndexBits ++ suffix

/-- A private output cursor differs from every scratch cell. -/
theorem encLinkOutput_separate (output scratch : Nat) (lower : 256 ≤ output)
    (upper : output < 2 ^ 96) (small : scratch < 256) :
    BitVec.ofNat 256 output ≠ BitVec.ofNat 256 scratch := by
  intro equal
  have values := congrArg BitVec.toNat equal
  have bound : output < 2 ^ 256 := lt_trans upper (by decide)
  have scratchBound : scratch < 2 ^ 256 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt scratchBound] at values
  omega

/-- The loop operand always has the source block width. -/
theorem encLinkInvariant_operand (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit) :
    (encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8 =
      (xor (encodeBit ((memory.ram 35).getLsbD 0)) firstKey).setWidth 256 := by
  rw [(encLinkPrepared_values memory index _).1, ready.whitening, encLink_lowBit]
  exact BitVec.setWidth_xor.symm

/-- The loop invariant supplies room for the next stored pair. -/
theorem encLinkInvariant_room (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (indices : List EncPRF.PermutationIndex) (suffix : List Bool)
    (firstKey : Block) (output limit : Nat)
    (ready : EncLinkLoopMemory state memory (index :: indices) suffix firstKey output limit) :
    2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) + 256 < 2 ^ 110 := by
  have count := ready.baseCount (encLinkPhysicalIndex index)
  have room := ready.room
  simp only [List.length_cons] at room
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
