import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block retains the prepared directive and all caller pointers. -/
def gateDirectiveSave : List LinearInstruction :=
  [.constant 0 16, .store 0 9, .constant 0 17, .store 0 4,
   .constant 0 18, .store 0 5, .constant 0 19, .store 0 6,
   .constant 0 20, .store 0 7, .constant 0 21, .store 0 11,
   .constant 0 22, .store 0 12, .constant 0 23, .store 0 13,
   .constant 0 24, .store 0 14, .constant 0 25, .store 0 15]

/-- The restore block recovers the caller pointers after internal oracle calls. -/
def gateDirectiveRestore : List LinearInstruction :=
  [.constant 0 21, .load 11 0, .constant 0 22, .load 12 0,
   .constant 0 23, .load 13 0, .constant 0 24, .load 14 0,
   .constant 0 25, .load 15 0]

/-- The slot loader supplies the saved input and target to one internal fixed-key call. -/
def gateSlotLoad (oracleIndex : Nat) (slot : Fin 3) : List LinearInstruction :=
  [.constant 0 16, .load 8 0,
   .constant 0 (BitVec.ofNat 256 (17 + slot.val)), .load 1 0,
   .constant 0 14, .store 0 1,
   .constant 9 (BitVec.ofNat 256 oracleIndex), .constant 10 0]

end Kriterion.ArgoMAC.ArithmeticSimulator
