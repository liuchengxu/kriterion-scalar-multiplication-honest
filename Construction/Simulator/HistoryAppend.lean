import Construction.Simulator.OverlayMetadata

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The history header occupies the fourth public table region. -/
def historyHeader (memory : Memory) : Word :=
  memory.registers 6 + BitVec.ofNat 256 (3 * 2 ^ 110)

/-- The setup selects the first free history pair. -/
def historyAppendSetup : List LinearInstruction :=
  [.constant 13 (BitVec.ofNat 256 (3 * 2 ^ 110)), .arithmetic .add 13 6 13,
   .load 12 13, .constant 14 2, .arithmetic .mul 9 12 14,
   .constant 14 256, .arithmetic .add 9 9 14, .arithmetic .add 9 13 9]

/-- The setup retains the domain and range in registers eight and ten. -/
def historyAppendReady (memory : Memory) : Memory :=
  let registers := Function.update memory.registers 13 (historyHeader memory)
  let registers := Function.update registers 12 (memory.ram (historyHeader memory))
  let registers := Function.update registers 14 256
  let registers := Function.update registers 9
    (historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256))
  { memory with registers := registers }

/-- The append block stores one public query or successful program pair. -/
def historyAppend : List LinearInstruction := historyAppendSetup ++ pairStore ++ overlayAppendFinish

/-- The source commits the appended history pair and increased count. -/
def historyAppended (memory : Memory) : Memory :=
  overlayAppendFinished (pairStored (historyAppendReady memory))

end Kriterion.ArgoMAC.ArithmeticSimulator
