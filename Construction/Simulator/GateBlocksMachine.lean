import Construction.Simulator.GateBlocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The hash branch returns after its 27 fixed instructions. -/
def gateHashLabels (index : Nat) : Fin 39 :=
  if inside : index < 27 then ⟨1 + index, by omega⟩ else 38

/-- The pad branch returns after its ten fixed instructions. -/
def gatePadLabels (index : Nat) : Fin 39 :=
  if inside : index < 10 then ⟨28 + index, by omega⟩ else 38

/-- The branch machine selects the source's hash or pad computation through register ten. -/
def gateBlocksMachine (tweak : Block) : Machine := ⟨38, Vector.ofFn (fun pc : Fin 39 =>
  if first : pc.val = 0 then .branch 10 1 28
  else if hash : pc.val < 28 then
    ((gateHashProgram tweak)[pc.val - 1]'(by change pc.val - 1 < 27; omega)).emit (gateHashLabels (pc.val - 1 + 1))
  else if pad : pc.val < 38 then
    ((gatePadProgram tweak)[pc.val - 28]'(by change pc.val - 28 < 10; omega)).emit (gatePadLabels (pc.val - 28 + 1))
  else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
