import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The link saves caller data in scratch cells 32 through 38 before its hash call. -/
def encLinkSave : List LinearInstruction :=
  [.constant 15 32, .store 15 11, .constant 15 33, .store 15 14,
    .constant 15 34, .store 15 14, .constant 15 35, .store 15 12,
    .constant 15 36, .store 15 13, .constant 2 508, .constant 15 38, .store 15 2,
    .constant 9 15748, .constant 10 4]

/-- The link stores the high hash block first and the low hash block second. -/
def encLinkWhitening : List LinearInstruction :=
  [.constant 1 128, .arithmetic .shiftRight 2 8 1, .constant 15 39, .store 15 2,
    .constant 1 (BitVec.ofNat 256 (2 ^ 128 - 1)), .arithmetic .and 2 8 1, .constant 15 40, .store 15 2]

/-- The link prepares one Even-Mansour query and saves its selected label. -/
def encLinkPrepare : List LinearInstruction :=
  [.constant 15 32, .load 1 15, .load 2 1, .constant 15 41, .store 15 2,
    .constant 15 35, .load 2 15, .constant 3 1, .arithmetic .and 4 2 3,
    .arithmetic .shiftRight 2 2 3, .store 15 2, .constant 15 39, .load 2 15,
    .arithmetic .xor 8 4 2, .constant 2 0, .arithmetic .add 9 0 2, .constant 10 2]

/-- The link transforms one accepted reply and advances both label pointers. -/
def encLinkFinish : List LinearInstruction :=
  [.constant 15 40, .load 1 15, .arithmetic .xor 8 8 1,
    .constant 15 41, .load 1 15, .arithmetic .xor 8 8 1,
    .constant 15 33, .load 2 15, .store 2 8, .constant 1 1,
    .arithmetic .add 2 2 1, .store 15 2, .constant 15 32,
    .load 2 15, .arithmetic .add 2 2 1, .store 15 2,
    .constant 15 38, .load 2 15, .arithmetic .sub 2 2 1, .store 15 2]

/-- The coordinate switch installs the y-coordinate bits after the first 254 labels. -/
def encLinkSwitch : List LinearInstruction :=
  [.constant 15 36, .load 2 15, .constant 15 35, .store 15 2]

/-- The return block restores the output-label base pointer for the point-gate loader. -/
def encLinkReturn : List LinearInstruction := [.constant 15 34, .load 14 15]

end Kriterion.ArgoMAC.ArithmeticSimulator
