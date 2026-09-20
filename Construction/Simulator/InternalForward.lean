import Construction.Simulator.StoredForward
import Construction.Simulator.OverlayMetadata
import Construction.Simulator.SwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

def internalForwardLabels (pc : Fin 179) : Fin 199 := ⟨pc.val, by omega⟩
def internalOverlayLoadLabels (index : Nat) : Fin 199 := ⟨179 + min index 5, by omega⟩
def internalOverlayScanLabels (pc : Fin 14) : Fin 199 := ⟨184 + pc.val, by omega⟩

/-- The internal query returns at 197 on success and at 198 on cutoff failure.
The query preserves all bit stacks. -/
def internalForward (attempts : Nat) : Machine := ⟨198, Vector.ofFn (fun pc : Fin 199 =>
  if forward : pc.val < 178 then
    relocate internalForwardLabels
      ((storedForward attempts).code[pc.val]'(by change pc.val < 179; omega))
  else if loader : 179 ≤ pc.val ∧ pc.val < 184 then
    (overlayLoad[pc.val - 179]'(by change pc.val - 179 < 5; omega)).emit
      (internalOverlayLoadLabels (pc.val - 179 + 1))
  else if scanner : 184 ≤ pc.val ∧ pc.val < 197 then
    relocate internalOverlayScanLabels
      (swapTable.code[pc.val - 184]'(by change pc.val - 184 < 14; omega))
  else if pc.val = 178 then .branch 7 198 179 else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
