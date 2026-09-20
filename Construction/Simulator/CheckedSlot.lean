import Construction.Simulator.HistoryFresh
import Construction.Simulator.InternalForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The start block saves the command and computes its public oracle header. -/
def checkedSlotStart : List LinearInstruction :=
  [.constant 0 26, .store 0 8, .constant 0 27, .store 0 9,
   .constant 0 14, .load 1 0, .constant 0 28, .store 0 1,
   .constant 6 (BitVec.ofNat 256 (2 ^ 112)), .arithmetic .mul 6 9 6,
   .constant 0 (BitVec.ofNat 256 (2 ^ 128)), .arithmetic .add 6 0 6]

/-- The restore block supplies the original command to the internal forward call. -/
def checkedSlotRestore : List LinearInstruction :=
  [.constant 0 26, .load 8 0, .constant 0 27, .load 9 0, .constant 10 0]

/-- The target block restores the requested range before the overlay append. -/
def checkedSlotTarget : List LinearInstruction :=
  [.constant 0 28, .load 1 0, .constant 0 14, .store 0 1]

/-- The history setup restores the requested pair after the overlay append. -/
def checkedSlotHistory : List LinearInstruction :=
  [.constant 0 26, .load 8 0, .constant 0 28, .load 10 0]

/-- The collision block records bad and leaves the public permutation unchanged. -/
def checkedSlotCollision : List LinearInstruction :=
  [.constant 0 31, .constant 1 1, .store 0 1]

def checkedSlotLinearLabels (start length : Nat) (bound : start + length < 305)
    (returnLabel : Fin 305) (pc : Nat) : Fin 305 :=
  if inside : pc < length then ⟨start + pc, by omega⟩ else returnLabel

def checkedSlotStartLabels := checkedSlotLinearLabels 0 12 (by decide) 12

def checkedSlotFreshLabels (pc : Fin 43) : Fin 305 :=
  if pc = 41 then 55 else ⟨12 + pc.val, by omega⟩

def checkedSlotRestoreLabels := checkedSlotLinearLabels 56 5 (by decide) 61

def checkedSlotForwardLabels (pc : Fin 199) : Fin 305 :=
  if pc = 197 then 260 else if pc = 198 then 304 else ⟨61 + pc.val, by omega⟩

def checkedSlotTargetLabels := checkedSlotLinearLabels 260 4 (by decide) 264

def checkedSlotOverlayLabels := checkedSlotLinearLabels 264 17 (by decide) 281

def checkedSlotHistoryLabels := checkedSlotLinearLabels 281 4 (by decide) 285

def checkedSlotAppendLabels := checkedSlotLinearLabels 285 15 (by decide) 300

def checkedSlotCollisionLabels := checkedSlotLinearLabels 301 3 (by decide) 300

/-- The checked slot machine skips collisions and stops on sampler cutoff.
Label 300 returns after a collision or a successful program. Label 304 returns cutoff failure. -/
def checkedSlot (attempts : Nat) : Machine := ⟨304, Vector.ofFn (fun pc : Fin 305 =>
  if start : pc.val < 12 then
    (checkedSlotStart[pc.val]'(by change pc.val < 12; omega)).emit (checkedSlotStartLabels (pc.val + 1))
  else if fresh : 12 ≤ pc.val ∧ pc.val < 55 then
    relocate checkedSlotFreshLabels (historyFresh.code[pc.val - 12]'(by change pc.val - 12 < 43; omega))
  else if restore : 56 ≤ pc.val ∧ pc.val < 61 then
    (checkedSlotRestore[pc.val - 56]'(by change pc.val - 56 < 5; omega)).emit
      (checkedSlotRestoreLabels (pc.val - 56 + 1))
  else if forward : 61 ≤ pc.val ∧ pc.val < 260 then
    relocate checkedSlotForwardLabels ((internalForward attempts).code[pc.val - 61]'(by change pc.val - 61 < 199; omega))
  else if target : 260 ≤ pc.val ∧ pc.val < 264 then
    (checkedSlotTarget[pc.val - 260]'(by change pc.val - 260 < 4; omega)).emit
      (checkedSlotTargetLabels (pc.val - 260 + 1))
  else if overlay : 264 ≤ pc.val ∧ pc.val < 281 then
    (overlayAppend[pc.val - 264]'(by change pc.val - 264 < 17; omega)).emit
      (checkedSlotOverlayLabels (pc.val - 264 + 1))
  else if history : 281 ≤ pc.val ∧ pc.val < 285 then
    (checkedSlotHistory[pc.val - 281]'(by change pc.val - 281 < 4; omega)).emit
      (checkedSlotHistoryLabels (pc.val - 281 + 1))
  else if append : 285 ≤ pc.val ∧ pc.val < 300 then
    (historyAppend[pc.val - 285]'(by change pc.val - 285 < 15; omega)).emit
      (checkedSlotAppendLabels (pc.val - 285 + 1))
  else if collision : 301 ≤ pc.val ∧ pc.val < 304 then
    (checkedSlotCollision[pc.val - 301]'(by change pc.val - 301 < 3; omega)).emit
      (checkedSlotCollisionLabels (pc.val - 301 + 1))
  else match pc.val with
    | 55 => .branch 7 301 56
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
