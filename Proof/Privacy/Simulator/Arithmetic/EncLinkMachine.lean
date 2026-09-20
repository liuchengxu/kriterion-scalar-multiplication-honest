import Construction.Simulator.EncLinkArithmetic
import Proof.Privacy.Simulator.Arithmetic.EncLinkIndexCode
import Construction.Simulator.InternalForward
import Construction.Simulator.HashHandler
import Construction.Simulator.WordInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

private theorem indexPreludeLength : encLinkIndexPrelude.length = 7112 := by
  have lengths : ∀ index, (encLinkIndexBits index).length = 14 := by intro index; simp [encLinkIndexBits]
  have wire : encLinkIndexWire.length = encLinkIndices.length * 14 := by
    unfold encLinkIndexWire
    induction encLinkIndices with
    | nil => simp
    | cons head tail ih => simp [lengths, ih, Nat.add_mul, Nat.add_comm]
  simpa [encLinkIndexPrelude, encLinkIndices, coordinateBitCount] using wire

/-- Each link block has one fixed range and a fixed return label. -/
def encLinkLabels (start length : Nat) (fits : start + length ≤ 7468)
    (next : Fin 7468) (index : Nat) : Fin 7468 :=
  if valid : index < length then ⟨start + index, by omega⟩ else next

def encLinkSaveLabels := encLinkLabels 0 15 (by decide) 15
def encLinkHashLabels (pc : Fin 74) := encLinkLabels 15 73 (by decide) 88 pc.val
def encLinkWhiteningLabels := encLinkLabels 88 8 (by decide) 96
def encLinkIndexLabels := encLinkLabels 96 7112 (by decide) 7208
def encLinkReaderLabels (pc : Fin 15) := encLinkLabels 7208 14 (by decide) 7222 pc.val
def encLinkPrepareLabels := encLinkLabels 7222 17 (by decide) 7239
def encLinkQueryLabels (pc : Fin 199) : Fin 7468 :=
  if valid : pc.val < 197 then ⟨7239 + pc.val, by omega⟩ else if pc.val = 197 then 7436 else 7467
def encLinkFinishLabels := encLinkLabels 7436 20 (by decide) 7456
def encLinkSwitchLabels := encLinkLabels 7460 4 (by decide) 7208
def encLinkReturnLabels := encLinkLabels 7464 2 (by decide) 7466

/-- The complete link runs one hash query and 508 programmed forward queries.
The link aborts at 7467 on any permutation cutoff failure.
The link returns at 7466 on success. -/
noncomputable def encLink (attempts : Nat) : Machine := ⟨7467, Vector.ofFn (fun pc : Fin 7468 =>
  if result : 7464 ≤ pc.val ∧ pc.val < 7466 then
    (encLinkReturn[pc.val - 7464]'(by change pc.val - 7464 < 2; omega)).emit
      (encLinkReturnLabels (pc.val - 7464 + 1))
  else if save : pc.val < 15 then
    (encLinkSave[pc.val]'(by change pc.val < 15; exact save)).emit (encLinkSaveLabels (pc.val + 1))
  else if hash : 15 ≤ pc.val ∧ pc.val < 88 then
    relocate encLinkHashLabels (hashHandler.code[pc.val - 15]'(by change pc.val - 15 < 74; omega))
  else if whitening : 88 ≤ pc.val ∧ pc.val < 96 then
    (encLinkWhitening[pc.val - 88]'(by change pc.val - 88 < 8; omega)).emit
      (encLinkWhiteningLabels (pc.val - 88 + 1))
  else if indices : 96 ≤ pc.val ∧ pc.val < 7208 then
    (encLinkIndexPrelude[pc.val - 96]'(by rw [indexPreludeLength]; omega)).emit
      (encLinkIndexLabels (pc.val - 96 + 1))
  else if reader : 7208 ≤ pc.val ∧ pc.val < 7222 then
    relocate encLinkReaderLabels ((wordInput 14).code[pc.val - 7208]'(by change pc.val - 7208 < 15; omega))
  else if prepare : 7222 ≤ pc.val ∧ pc.val < 7239 then
    (encLinkPrepare[pc.val - 7222]'(by change pc.val - 7222 < 17; omega)).emit
      (encLinkPrepareLabels (pc.val - 7222 + 1))
  else if query : 7239 ≤ pc.val ∧ pc.val < 7436 then
    relocate encLinkQueryLabels
      ((internalForward attempts).code[pc.val - 7239]'(by change pc.val - 7239 < 199; omega))
  else if finish : 7436 ≤ pc.val ∧ pc.val < 7456 then
    (encLinkFinish[pc.val - 7436]'(by change pc.val - 7436 < 20; omega)).emit
      (encLinkFinishLabels (pc.val - 7436 + 1))
  else if switch : 7460 ≤ pc.val ∧ pc.val < 7464 then
    (encLinkSwitch[pc.val - 7460]'(by change pc.val - 7460 < 4; omega)).emit
      (encLinkSwitchLabels (pc.val - 7460 + 1))
  else match pc.val with
    | 7456 => .branch 2 7464 7457
    | 7457 => .constant 3 254 7458
    | 7458 => .arithmetic .xor 3 2 3 7459
    | 7459 => .branch 3 7460 7208
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
