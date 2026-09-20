import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The machine applies the stored transpositions in reverse address order.
Register eight holds the value. Register nine holds the first RAM address.
Register ten holds the pair count. Registers eleven through fifteen hold temporary values. -/
def reverseSwapTable : Machine := ⟨14, #v[
  .constant 15 3 14,
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
  .arithmetic .sub 9 9 15 12,
  .arithmetic .sub 10 10 14 1,
  .halt,
  .constant 14 1 1], by decide⟩

/-- The source applies the transpositions stored in RAM pairs in reverse address order. -/
def applyReverseTableSwaps : Nat → (Word → Word) → Word → Word → Word
  | 0, _, _, value => value
  | count + 1, ram, address, value =>
      applyReverseTableSwaps count ram (address - 2#256)
        (Equiv.swap (ram address) (ram (address + 1#256)) value)

/-- The representation stores one pair in each two-cell RAM entry. -/
def RepresentsReversePairs (ram : Word → Word) : Word → List (Word × Word) → Prop
  | _, [] => True
  | address, pair :: rest =>
      ram address = pair.1 ∧ ram (address + 1#256) = pair.2 ∧ RepresentsReversePairs ram (address - 2#256) rest

end Kriterion.ArgoMAC.ArithmeticSimulator
