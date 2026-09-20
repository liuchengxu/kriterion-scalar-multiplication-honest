import Construction.Simulator.QueryInput
import Construction.Simulator.StoredInverse
import Construction.Simulator.HashHandler
import Construction.Simulator.HashOutput
import Construction.Simulator.OverlayMetadata

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

private theorem outputLength (width : Nat) : (wordOutput width).length = 3 * width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [wordOutput, ih, Nat.mul_add]

private theorem hashLength : hashOutput.length = 770 := by
  simp [hashOutput, hashOutputShift, outputLength]

/-- Each block uses its assigned table range and an explicit caller return. -/
def publicHandlerLabels (start length : Nat) (fits : start + length ≤ 1772)
    (returnLabel : Fin 1772) (index : Nat) : Fin 1772 :=
  if inside : index < length then ⟨start + index, by omega⟩ else returnLabel

def publicQueryLabels (pc : Fin 97) : Fin 1772 :=
  publicHandlerLabels 0 96 (by decide) 96 pc.val
def publicForwardLabels (pc : Fin 179) : Fin 1772 :=
  publicHandlerLabels 102 178 (by decide) 280 pc.val
def publicOverlayLoadLabels := publicHandlerLabels 281 5 (by decide) 286
def publicOverlayScanLabels (pc : Fin 14) : Fin 1772 :=
  publicHandlerLabels 286 13 (by decide) 616 pc.val
def publicInverseHeaderLabels := publicHandlerLabels 299 22 (by decide) 321
def publicInverseOverlayLoadLabels := publicHandlerLabels 321 9 (by decide) 330
def publicInverseOverlayScanLabels (pc : Fin 15) : Fin 1772 :=
  if pc = 13 then 345 else ⟨330 + pc.val, by omega⟩
def publicQueryRestoreLabels := publicHandlerLabels 345 4 (by decide) 349
def publicInverseLabels (pc : Fin 193) : Fin 1772 :=
  publicHandlerLabels 349 192 (by decide) 541 pc.val
def publicHashLabels (pc : Fin 74) : Fin 1772 :=
  publicHandlerLabels 542 73 (by decide) 615 pc.val
def publicBlockOutputLabels := publicHandlerLabels 616 384 (by decide) 1770
def publicHashOutputLabels := publicHandlerLabels 1000 770 (by decide) 1770

/-- The public handler reads a query, applies the programmed oracle, and writes its wire answer.
The handler halts without an answer when the permutation sampler rejects every trial. -/
def publicHandler (attempts : Nat) : Machine := ⟨1771, Vector.ofFn (fun pc : Fin 1772 =>
  if query : pc.val < 96 then
    relocate publicQueryLabels (queryInput.code[pc.val]'(by change pc.val < 97; omega))
  else if forward : 102 ≤ pc.val ∧ pc.val < 280 then
    relocate publicForwardLabels ((storedForward attempts).code[pc.val - 102]'(by change pc.val - 102 < 179; omega))
  else if overlayLoad : 281 ≤ pc.val ∧ pc.val < 286 then
    (ArithmeticSimulator.overlayLoad[pc.val - 281]'(by change pc.val - 281 < 5; omega)).emit
      (publicOverlayLoadLabels (pc.val - 281 + 1))
  else if overlayScan : 286 ≤ pc.val ∧ pc.val < 299 then
    relocate publicOverlayScanLabels (swapTable.code[pc.val - 286]'(by change pc.val - 286 < 14; omega))
  else if inverseHeader : 299 ≤ pc.val ∧ pc.val < 321 then
    (oracleLoad[pc.val - 299]'(by change pc.val - 299 < 22; omega)).emit
      (publicInverseHeaderLabels (pc.val - 299 + 1))
  else if inverseLoad : 321 ≤ pc.val ∧ pc.val < 330 then
    (overlayInverseLoad[pc.val - 321]'(by change pc.val - 321 < 9; omega)).emit
      (publicInverseOverlayLoadLabels (pc.val - 321 + 1))
  else if inverseScan : 330 ≤ pc.val ∧ pc.val < 345 then
    relocate publicInverseOverlayScanLabels
      (reverseSwapTable.code[pc.val - 330]'(by change pc.val - 330 < 15; omega))
  else if restore : 345 ≤ pc.val ∧ pc.val < 349 then
    (queryRestore[pc.val - 345]'(by change pc.val - 345 < 4; omega)).emit
      (publicQueryRestoreLabels (pc.val - 345 + 1))
  else if inverse : 349 ≤ pc.val ∧ pc.val < 541 then
    relocate publicInverseLabels ((storedInverse attempts).code[pc.val - 349]'(by change pc.val - 349 < 193; omega))
  else if hash : 542 ≤ pc.val ∧ pc.val < 615 then
    relocate publicHashLabels (hashHandler.code[pc.val - 542]'(by change pc.val - 542 < 74; omega))
  else if blockOutput : 616 ≤ pc.val ∧ pc.val < 1000 then
    ((wordOutput 128)[pc.val - 616]'(by rw [outputLength]; omega)).emit
      (publicBlockOutputLabels (pc.val - 616 + 1))
  else if hashOutput : 1000 ≤ pc.val ∧ pc.val < 1770 then
    (ArithmeticSimulator.hashOutput[pc.val - 1000]'(by rw [hashLength]; omega)).emit
      (publicHashOutputLabels (pc.val - 1000 + 1))
  else match pc.val with
    | 96 => .constant 14 4 97
    | 97 => .arithmetic .xor 13 10 14 98
    | 98 => .branch 13 542 99
    | 99 => .constant 14 1 100
    | 100 => .arithmetic .and 13 10 14 101
    | 101 => .branch 13 102 299
    | 280 => .branch 7 1771 281
    | 541 => .branch 7 1771 616
    | 615 => .branch 7 1771 1000
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
