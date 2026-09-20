import Construction.Simulator.LinearProgram
import Construction.ArgoMAC.EncPRF

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The link visits the selected labels in x-then-y order. -/
def encLinkIndices : List EncPRF.PermutationIndex :=
  (List.finRange coordinateBitCount).map (fun index => (EncPRF.Coordinate.x, index)) ++
    (List.finRange coordinateBitCount).map (fun index => (EncPRF.Coordinate.y, index))

/-- The link uses the same finite index encoding as the public protocol. -/
noncomputable def encLinkIndexValue (index : EncPRF.PermutationIndex) : Nat :=
  (Fintype.equivFin EncPRF.PermutationIndex index).val + 15240

/-- Each fixed index uses fourteen little-endian bits. -/
noncomputable def encLinkIndexBits (index : EncPRF.PermutationIndex) : List Bool :=
  (List.finRange 14).map (BitVec.ofNat 14 (encLinkIndexValue index)).getLsb

/-- The complete fixed schedule contains 508 oracle indices. -/
noncomputable def encLinkIndexWire : List Bool := encLinkIndices.flatMap encLinkIndexBits

/-- The prelude pushes its fixed schedule through charged instructions. -/
noncomputable def encLinkIndexPrelude : List LinearInstruction :=
  encLinkIndexWire.reverse.map (LinearInstruction.push 0)

end Kriterion.ArgoMAC.ArithmeticSimulator
