import Construction.Simulator.HistoryAppend
import Construction.Simulator.TableLookup
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The domain loader selects all recorded domain cells. -/
def historyDomainLoad : List LinearInstruction :=
  [.constant 9 (BitVec.ofNat 256 (3 * 2 ^ 110)), .arithmetic .add 9 6 9,
   .load 10 9, .constant 14 256, .arithmetic .add 9 9 14]

/-- The range loader selects all recorded range cells and the requested target. -/
def historyRangeLoad : List LinearInstruction :=
  [.constant 9 (BitVec.ofNat 256 (3 * 2 ^ 110)), .arithmetic .add 9 6 9,
   .load 10 9, .constant 14 257, .arithmetic .add 9 9 14,
   .constant 15 14, .load 8 15]

/-- The domain lookup returns to the collision branch. -/
def historyDomainLabels (pc : Fin 13) : Fin 43 :=
  if pc = 9 then 18 else ⟨5 + pc.val, by omega⟩

/-- The range lookup returns to the acceptance flag computation. -/
def historyRangeLabels (pc : Fin 13) : Fin 43 :=
  if pc = 9 then 39 else ⟨26 + pc.val, by omega⟩

def historyDomainLoadLabels (pc : Nat) : Fin 43 :=
  if inside : pc < 5 then ⟨pc, by omega⟩ else 5

def historyRangeLoadLabels (pc : Nat) : Fin 43 :=
  if inside : pc < 7 then ⟨19 + pc, by omega⟩ else 26

/-- The freshness machine rejects any recorded domain or range collision.
Register eight holds the domain. Scratch cell fourteen holds the range.
Register six holds the oracle header. Register seven returns the acceptance flag. -/
def historyFresh : Machine := ⟨42, Vector.ofFn (fun pc : Fin 43 =>
  if domainLoad : pc.val < 5 then
    (historyDomainLoad[pc.val]'(by change pc.val < 5; omega)).emit (historyDomainLoadLabels (pc.val + 1))
  else if domain : 5 ≤ pc.val ∧ pc.val < 18 then
    relocate historyDomainLabels (tableLookup.code[pc.val - 5]'(by change pc.val - 5 < 13; omega))
  else if rangeLoad : 19 ≤ pc.val ∧ pc.val < 26 then
    (historyRangeLoad[pc.val - 19]'(by change pc.val - 19 < 7; omega)).emit
      (historyRangeLoadLabels (pc.val - 19 + 1))
  else if range : 26 ≤ pc.val ∧ pc.val < 39 then
    relocate historyRangeLabels (tableLookup.code[pc.val - 26]'(by change pc.val - 26 < 13; omega))
  else match pc.val with
    | 18 => .branch 12 19 42
    | 39 => .constant 7 1 40
    | 40 => .arithmetic .xor 7 12 7 41
    | 42 => .constant 7 0 41
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
