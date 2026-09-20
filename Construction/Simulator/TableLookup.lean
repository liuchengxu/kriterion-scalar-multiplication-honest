import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The lookup scans consecutive RAM key-value pairs.
Register eight holds the key. Register nine holds the first address.
Register ten holds the entry count. Registers eleven and twelve return the value and flag.
Registers thirteen through fifteen hold temporary values. -/
def tableLookup : Machine := ⟨12, #v[
  .constant 14 1 1,
  .constant 15 2 2,
  .branch 10 8 3,
  .load 13 9 4,
  .arithmetic .xor 13 13 8 5,
  .branch 13 10 6,
  .arithmetic .add 9 9 15 7,
  .arithmetic .sub 10 10 14 2,
  .constant 12 0 9,
  .halt,
  .arithmetic .add 9 9 14 11,
  .load 11 9 12,
  .constant 12 1 9], by decide⟩

/-- The table source returns the first matching value. -/
def findTable : Nat → (Word → Word) → Word → Word → Option Word
  | 0, _, _, _ => none
  | count + 1, ram, address, key =>
      if ram address = key then some (ram (address + 1))
      else findTable count ram (address + 2) key

end Kriterion.ArgoMAC.ArithmeticSimulator
