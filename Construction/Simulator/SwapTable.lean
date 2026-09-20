import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The machine applies every stored transposition in order.
Register eight holds the value. Register nine holds the first RAM address.
Register ten holds the pair count. Registers eleven through fourteen hold temporary values. -/
def swapTable : Machine := ⟨13, #v[
  .constant 14 1 1,
  .branch 10 13 2,
  .load 11 9 3,
  .arithmetic .add 9 9 14 4,
  .load 12 9 5,
  .arithmetic .xor 13 8 11 6,
  .branch 13 9 7,
  .arithmetic .xor 13 8 12 8,
  .branch 13 10 11,
  .arithmetic .add 8 12 13 11,
  .arithmetic .add 8 11 13 11,
  .arithmetic .add 9 9 14 12,
  .arithmetic .sub 10 10 14 1,
  .halt], by decide⟩

/-- The source applies the transpositions stored in consecutive RAM cells. -/
def applyTableSwaps : Nat → (Word → Word) → Word → Word → Word
  | 0, _, _, value => value
  | count + 1, ram, address, value =>
      applyTableSwaps count ram (address + 2#256)
        (Equiv.swap (ram address) (ram (address + 1#256)) value)

/-- The representation stores one pair in each two-cell RAM entry. -/
def RepresentsPairs (ram : Word → Word) : Word → List (Word × Word) → Prop
  | _, [] => True
  | address, pair :: rest =>
      ram address = pair.1 ∧ ram (address + 1#256) = pair.2 ∧ RepresentsPairs ram (address + 2#256) rest

end Kriterion.ArgoMAC.ArithmeticSimulator
