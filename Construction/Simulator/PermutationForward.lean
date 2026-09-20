import Construction.Simulator.KnownQuery
import Construction.Simulator.FreshQuery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward handler returns known answers and installs fresh answers. -/
def permutationForward (attempts : Nat) : Machine := ⟨153, Vector.ofFn (fun pc =>
  if known : pc.val < 38 then
    relocate (fun label : Fin 39 => (⟨label.val, by omega⟩ : Fin 154))
      (knownQuery.code[pc.val]'(by change pc.val < 39; omega))
  else if fresh : 39 ≤ pc.val ∧ pc.val < 153 then
    relocate (fun label : Fin 115 => (⟨label.val + 39, by omega⟩ : Fin 154))
      ((freshQuery attempts).code[pc.val - 39]'(by change pc.val - 39 < 115; omega))
  else if pc.val = 38 then .branch 7 39 153 else .halt), by decide⟩

def permutationKnownLabels (pc : Fin 39) : Fin 154 := ⟨pc.val, by omega⟩
def permutationFreshLabels (pc : Fin 115) : Fin 154 := ⟨pc.val + 39, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
