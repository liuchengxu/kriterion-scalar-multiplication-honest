import Construction.Simulator.PublicHandler
import Construction.Simulator.PublicHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The core keeps its physical instruction addresses. -/
def recordedPublicCore (pc : Fin 1772) : Fin 1810 := ⟨pc.val, by omega⟩

/-- The two entry edges insert the save block and the history block. -/
def recordedPublicRedirect (pc : Fin 1772) : Fin 1810 :=
  if pc = 96 then 1772 else if pc = 616 then 1776 else recordedPublicCore pc

/-- The save block returns directly to the core dispatcher. -/
def recordedPublicSaveLabels (index : Nat) : Fin 1810 :=
  if inside : index < 4 then ⟨1772 + index, by omega⟩ else 96

/-- The history block returns directly to the core answer writer. -/
def recordedPublicHistoryLabels (pc : Fin 35) : Fin 1810 :=
  if inside : pc.val < 34 then ⟨1776 + pc.val, by omega⟩ else 616

/-- The handler records each accepted external fixed-key query before its answer. -/
def recordedPublicHandler (attempts : Nat) : Machine := ⟨1809,
  Vector.ofFn (fun pc : Fin 1810 =>
    if core : pc.val < 1772 then
      relocate recordedPublicRedirect ((publicHandler attempts).code[pc.val]'core)
    else if save : pc.val < 1776 then
      (publicHistorySave[pc.val - 1772]'(by change pc.val - 1772 < 4; omega)).emit
        (recordedPublicSaveLabels (pc.val - 1772 + 1))
    else relocate recordedPublicHistoryLabels
      (publicHistory.code[pc.val - 1776]'(by change pc.val - 1776 < 35; omega))), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
