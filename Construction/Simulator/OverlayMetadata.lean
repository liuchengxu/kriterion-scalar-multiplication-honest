import Construction.Simulator.PairStore

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The overlay header occupies the third public table region. -/
def overlayHeader (memory : Memory) : Word :=
  memory.registers 6 + BitVec.ofNat 256 (2 ^ 111)

/-- The loader supplies the ascending overlay table to either swap scan. -/
def overlayLoad : List LinearInstruction :=
  [.constant 9 (BitVec.ofNat 256 (2 ^ 111)), .arithmetic .add 9 6 9,
    .load 10 9, .constant 14 256, .arithmetic .add 9 9 14]

/-- The loaded source preserves the answer, header, and acceptance flag. -/
def overlayLoaded (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update memory.registers
    9 (overlayHeader memory + 256#256)) 10 (memory.ram (overlayHeader memory))) 14 256 }

/-- The reverse setup moves the table pointer to the last stored pair. -/
def overlayReverseSetup : List LinearInstruction :=
  [.constant 14 2, .arithmetic .mul 15 10 14,
    .arithmetic .add 9 9 15, .arithmetic .sub 9 9 14]

/-- The reverse setup source retains the table count and the query operand. -/
def overlayReverseReady (memory : Memory) : Memory :=
  { memory with registers := (Function.update (Function.update (Function.update memory.registers
    14 2) 15 (memory.registers 10 * 2#256))
      9 (memory.registers 9 + memory.registers 10 * 2#256 - 2#256)) }

/-- The inverse loader selects the final pair in the ascending overlay table. -/
def overlayInverseLoad : List LinearInstruction := overlayLoad ++ overlayReverseSetup

/-- The inverse loader source preserves all caller registers below nine. -/
def overlayInverseLoaded (memory : Memory) : Memory := overlayReverseReady (overlayLoaded memory)

/-- The query restore block recovers the saved public index and tag. -/
def queryRestore : List LinearInstruction :=
  [.constant 15 9, .load 9 15, .constant 15 12, .load 10 15]

/-- The restored source retains the operand from the inverse overlay scan. -/
def queryRestored (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update memory.registers
    9 (memory.ram 9)) 10 (memory.ram 12)) 15 12 }

/-- The append setup places the current answer and the saved target after the existing pairs. -/
def overlayAppendSetup : List LinearInstruction :=
  [.constant 13 (BitVec.ofNat 256 (2 ^ 111)), .arithmetic .add 13 6 13,
    .load 12 13, .constant 14 2, .arithmetic .mul 9 12 14,
    .constant 14 256, .arithmetic .add 9 9 14, .arithmetic .add 9 13 9,
    .constant 15 14, .load 10 15]

/-- The append setup reads the programmed target from scratch cell fourteen. -/
def overlayAppendReady (memory : Memory) : Memory :=
  let registers := Function.update memory.registers 13 (overlayHeader memory)
  let registers := Function.update registers 12 (memory.ram (overlayHeader memory))
  let registers := Function.update registers 14 256
  let registers := Function.update registers 9
    (overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256))
  let registers := Function.update registers 15 14
  { memory with registers := Function.update registers 10 (memory.ram 14) }

/-- The append finish block commits the increased pair count. -/
def overlayAppendFinish : List LinearInstruction :=
  [.arithmetic .add 12 12 14, .store 13 12]

/-- The append finish source changes the header after the pair store. -/
def overlayAppendFinished (memory : Memory) : Memory :=
  { memory with
    registers := (Function.update memory.registers 12 (memory.registers 12 + memory.registers 14))
    ram := Function.update memory.ram (memory.registers 13) (memory.registers 12 + memory.registers 14) }

/-- The append block adds one swap and commits its count in seventeen instructions. -/
def overlayAppend : List LinearInstruction := overlayAppendSetup ++ pairStore ++ overlayAppendFinish

/-- The source appends a swap from the current answer to the programmed target. -/
def overlayAppended (memory : Memory) : Memory :=
  overlayAppendFinished (pairStored (overlayAppendReady memory))

end Kriterion.ArgoMAC.ArithmeticSimulator
