import Construction.ArgoMAC.BitAdaptor
import Construction.Simulator.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A fixed wire segment emits a fixed number of bits. The transmitted layout
writes one field element or one ciphertext row at its exact 254-bit payload width
and byte-aligns each group with a pad shorter than a byte, so a segment carries
its own width instead of always filling a whole word. -/
inductive WireSegment
  /-- This segment emits the `coordinateBitCount` low bits of the word at `offset`. -/
  | stored (offset : Word)
  /-- This segment emits `width` zero bits. A pad byte-aligns a group, so it is
  shorter than one byte. -/
  | zero (width : Fin 8)

/-- The segment emits exactly this many bits. -/
def WireSegment.width : WireSegment → Nat
  | .stored _ => coordinateBitCount
  | .zero width => width.val

/-- The segment costs this many instructions besides one per emitted bit. -/
def WireSegment.overhead : WireSegment → Nat
  | .stored _ => 3
  | .zero _ => 1

/-- The segment loads its value and emits its fixed number of bits.
Register eleven supplies the first address of the source data. -/
def WireSegment.program : WireSegment → List LinearInstruction
  | .stored offset =>
      [.constant 9 offset, .arithmetic .add 9 11 9, .load 8 9] ++ wordOutput coordinateBitCount
  | .zero width => [.constant 8 0] ++ wordOutput width

/-- The emitter processes segments in reverse order because each output bit is prepended. -/
def wireSegmentsProgram (segments : List WireSegment) : List LinearInstruction :=
  segments.reverse.flatMap WireSegment.program

end Kriterion.ArgoMAC.ArithmeticSimulator
