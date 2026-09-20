import Construction.Simulator.HistoryAppend
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block retains the external operand and tag before any oracle work. -/
def publicHistorySave : List LinearInstruction :=
  [.constant 15 48, .store 15 8, .constant 15 49, .store 15 10]

/-- The forward setup orders the saved operand and reply as a domain-range pair. -/
def publicHistoryForward : List LinearInstruction :=
  [.constant 15 50, .store 15 8, .constant 15 0, .arithmetic .add 10 8 15,
    .constant 15 48, .load 8 15]

/-- The inverse setup orders the reply and saved operand as a domain-range pair. -/
def publicHistoryInverse : List LinearInstruction :=
  [.constant 15 50, .store 15 8, .constant 15 48, .load 10 15]

/-- The restore block retains the actual reply after the history append. -/
def publicHistoryRestore : List LinearInstruction :=
  [.constant 15 50, .load 8 15]

/-- Each linear history block returns to its assigned caller label. -/
def publicHistoryLabels (start length : Nat) (fits : start + length ≤ 35)
    (next : Fin 35) (index : Nat) : Fin 35 :=
  if valid : index < length then ⟨start + index, by omega⟩ else next

def publicHistoryForwardLabels := publicHistoryLabels 7 6 (by decide) 17
def publicHistoryInverseLabels := publicHistoryLabels 13 4 (by decide) 17
def publicHistoryAppendLabels := publicHistoryLabels 17 15 (by decide) 32
def publicHistoryRestoreLabels := publicHistoryLabels 32 2 (by decide) 34

/-- The history tail records only accepted external fixed-key queries. -/
def publicHistory : Machine := ⟨34, Vector.ofFn (fun pc : Fin 35 =>
  if forward : 7 ≤ pc.val ∧ pc.val < 13 then
    (publicHistoryForward[pc.val - 7]'(by change pc.val - 7 < 6; omega)).emit
      (publicHistoryForwardLabels (pc.val - 7 + 1))
  else if inverse : 13 ≤ pc.val ∧ pc.val < 17 then
    (publicHistoryInverse[pc.val - 13]'(by change pc.val - 13 < 4; omega)).emit
      (publicHistoryInverseLabels (pc.val - 13 + 1))
  else if append : 17 ≤ pc.val ∧ pc.val < 32 then
    (historyAppend[pc.val - 17]'(by change pc.val - 17 < 15; omega)).emit
      (publicHistoryAppendLabels (pc.val - 17 + 1))
  else if restore : 32 ≤ pc.val ∧ pc.val < 34 then
    (publicHistoryRestore[pc.val - 32]'(by change pc.val - 32 < 2; omega)).emit
      (publicHistoryRestoreLabels (pc.val - 32 + 1))
  else match pc.val with
    | 0 => .branch 7 34 1
    | 1 => .constant 15 49 2
    | 2 => .load 0 15 3
    | 3 => .branch 0 7 4
    | 4 => .constant 1 1 5
    | 5 => .arithmetic .sub 0 0 1 6
    | 6 => .branch 0 13 34
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
