import Construction.Simulator.ClampPoint
import Construction.Simulator.HomogeneousRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The Horner block starts at the machine entry. -/
def targetHornerLabels (pc : Fin 1986) : Fin 4289 := ⟨pc.val, by omega⟩

/-- The correction block follows the Horner block. -/
def targetClampLabels (pc : Fin 27) : Fin 4289 := ⟨1985 + pc.val, by omega⟩

/-- The row block follows the scale-pointer instruction. -/
def targetRowLabels (pc : Fin 2277) : Fin 4289 := ⟨2012 + pc.val, by omega⟩

/-- The machine computes all output targets from the sampled points and scales.
Register ten points to the free points. Register eleven points to the input record.
Register fourteen points to the scales. Register thirteen points to the destination.
The Horner pass runs over the 90 free points; the row pass stores the first
accumulator point and those 90 points, so it converts 91 rows. -/
def outputTargetsMachine : Machine := ⟨4288, Vector.ofFn (fun pc : Fin 4289 =>
  if horner : pc.val < 1985 then
    relocate targetHornerLabels ((pointHornerMachine 90 (by decide)).code[pc.val]'(by change pc.val < 1986; omega))
  else if correction : pc.val < 2011 then
    relocate targetClampLabels (clampPoint.code[pc.val - 1985]'(by change pc.val - 1985 < 27; omega))
  else if pointer : pc.val = 2011 then .arithmetic .add 11 14 9 2012
  else if rows : pc.val < 4288 then
    relocate targetRowLabels ((homogeneousRows 90 (by decide)).code[pc.val - 2012]'(by change pc.val - 2012 < 2277; omega))
  else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
