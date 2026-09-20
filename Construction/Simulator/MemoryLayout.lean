import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The machine reserves the first 256 cells for temporary data. -/
def scratchLimit : Nat := 256

/-- The private source starts above the temporary data. -/
def privateBase : Nat := 2 ^ 64

/-- Each public oracle has four independent table regions. -/
def oracleCell (oracle : Fin 15749) (table : Fin 4) (offset : Nat) : Nat :=
  2 ^ 128 + oracle.val * 2 ^ 112 + table.val * 2 ^ 110 + offset

/-- The machine represents each table address as one 256-bit word. -/
def oracleAddress (oracle : Fin 15749) (table : Fin 4) (offset : Nat) : Word :=
  BitVec.ofNat 256 (oracleCell oracle table offset)

end Kriterion.ArgoMAC.ArithmeticSimulator
