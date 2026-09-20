import Construction.Simulator.CheckedSlot
import Construction.Simulator.GateDirectiveLoad
import Construction.Simulator.GateDirectiveScratch
import Construction.Simulator.GateBlocksMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Each static gate record fixes its RAM offsets and its three public oracle indices. -/
structure GateCode where
  selected : Fin 508
  target : Nat
  quotient : Nat
  table : Nat
  tweak : Block
  oracle : Fin 3 → Nat

/-- The slot-count test selects a third call only for a false input bit. -/
def gateDriverTest : List LinearInstruction :=
  [.constant 0 20, .load 1 0, .constant 2 3, .arithmetic .xor 1 1 2]

def gateDriverLinearLabels (start length : Nat) (bound : start + length < 1036)
    (returnLabel : Fin 1036) (pc : Nat) : Fin 1036 :=
  if inside : pc < length then ⟨start + pc, by omega⟩ else returnLabel

def gateDriverLoadLabels := gateDriverLinearLabels 0 21 (by decide) 21

def gateDriverBlocksLabels (pc : Fin 39) : Fin 1036 :=
  if pc = 38 then 60 else ⟨21 + pc.val, by omega⟩

def gateDriverSaveLabels := gateDriverLinearLabels 60 20 (by decide) 80

def gateDriverSlotLoadLabels (slot : Fin 3) : Nat → Fin 1036 :=
  match slot.val with
  | 0 => gateDriverLinearLabels 80 8 (by decide) 88
  | 1 => gateDriverLinearLabels 393 8 (by decide) 401
  | _ => gateDriverLinearLabels 711 8 (by decide) 719

def gateDriverSlotLabels (slot : Fin 3) (pc : Fin 305) : Fin 1036 :=
  if pc = 304 then 1035 else
  match slot.val with
  | 0 => if pc = 300 then 393 else ⟨88 + pc.val, by omega⟩
  | 1 => if pc = 300 then 706 else ⟨401 + pc.val, by omega⟩
  | _ => if pc = 300 then 1024 else ⟨719 + pc.val, by omega⟩

def gateDriverTestLabels := gateDriverLinearLabels 706 4 (by decide) 710

def gateDriverRestoreLabels := gateDriverLinearLabels 1024 10 (by decide) 1034

/-- The gate machine executes two or three checked slots in source order.
The machine restores all caller pointers before its normal return.
Label 1034 returns normally. Label 1035 returns sampler cutoff. -/
def gateDriver (attempts : Nat) (gate : GateCode) : Machine := ⟨1035, Vector.ofFn (fun pc : Fin 1036 =>
  if load : pc.val < 21 then
    ((gateDirectiveLoad gate.selected gate.target gate.quotient gate.table)[pc.val]'(by change pc.val < 21; omega)).emit
      (gateDriverLoadLabels (pc.val + 1))
  else if blocks : 21 ≤ pc.val ∧ pc.val < 60 then
    relocate gateDriverBlocksLabels ((gateBlocksMachine gate.tweak).code[pc.val - 21]'(by change pc.val - 21 < 39; omega))
  else if save : 60 ≤ pc.val ∧ pc.val < 80 then
    (gateDirectiveSave[pc.val - 60]'(by change pc.val - 60 < 20; omega)).emit (gateDriverSaveLabels (pc.val - 60 + 1))
  else if load0 : 80 ≤ pc.val ∧ pc.val < 88 then
    ((gateSlotLoad (gate.oracle 0) 0)[pc.val - 80]'(by change pc.val - 80 < 8; omega)).emit
      (gateDriverSlotLoadLabels 0 (pc.val - 80 + 1))
  else if slot0 : 88 ≤ pc.val ∧ pc.val < 393 then
    relocate (gateDriverSlotLabels 0) ((checkedSlot attempts).code[pc.val - 88]'(by change pc.val - 88 < 305; omega))
  else if load1 : 393 ≤ pc.val ∧ pc.val < 401 then
    ((gateSlotLoad (gate.oracle 1) 1)[pc.val - 393]'(by change pc.val - 393 < 8; omega)).emit
      (gateDriverSlotLoadLabels 1 (pc.val - 393 + 1))
  else if slot1 : 401 ≤ pc.val ∧ pc.val < 706 then
    relocate (gateDriverSlotLabels 1) ((checkedSlot attempts).code[pc.val - 401]'(by change pc.val - 401 < 305; omega))
  else if test : 706 ≤ pc.val ∧ pc.val < 710 then
    (gateDriverTest[pc.val - 706]'(by change pc.val - 706 < 4; omega)).emit (gateDriverTestLabels (pc.val - 706 + 1))
  else if load2 : 711 ≤ pc.val ∧ pc.val < 719 then
    ((gateSlotLoad (gate.oracle 2) 2)[pc.val - 711]'(by change pc.val - 711 < 8; omega)).emit
      (gateDriverSlotLoadLabels 2 (pc.val - 711 + 1))
  else if slot2 : 719 ≤ pc.val ∧ pc.val < 1024 then
    relocate (gateDriverSlotLabels 2) ((checkedSlot attempts).code[pc.val - 719]'(by change pc.val - 719 < 305; omega))
  else if restore : 1024 ≤ pc.val ∧ pc.val < 1034 then
    (gateDirectiveRestore[pc.val - 1024]'(by change pc.val - 1024 < 10; omega)).emit
      (gateDriverRestoreLabels (pc.val - 1024 + 1))
  else match pc.val with
    | 710 => .branch 1 711 1024
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
