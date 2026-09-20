import Construction.Simulator.LinearProgram
import Construction.Simulator.MemoryLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The header address uses the public oracle index and its fixed region stride. -/
def oracleHeader (index : Word) : Word :=
  BitVec.ofNat 256 (2 ^ 128) + index * BitVec.ofNat 256 (2 ^ 112)

/-- The loader retains the oracle index, query tag, and header address in scratch RAM. -/
def oracleLoadRam (memory : Memory) : Word → Word :=
  Function.update (Function.update (Function.update memory.ram 9 (memory.registers 9))
    12 (memory.registers 10)) 13 (oracleHeader (memory.registers 9))

/-- The loader reads the used count and computes both descending table addresses. -/
def oracleLoadSetup : List LinearInstruction :=
  [.constant 15 9, .store 15 9, .constant 15 12, .store 15 10,
    .constant 6 (BitVec.ofNat 256 (2 ^ 112)), .arithmetic .mul 6 9 6,
    .constant 1 (BitVec.ofNat 256 (2 ^ 128)), .arithmetic .add 6 1 6,
    .constant 15 13, .store 15 6]

/-- The second loader block reads the header and computes the table bases. -/
def oracleLoadFinish : List LinearInstruction :=
  [.load 0 6, .constant 7 0,
    .arithmetic .add 2 0 7, .arithmetic .add 4 0 7,
    .constant 5 (BitVec.ofNat 256 (2 ^ 128)), .constant 1 (BitVec.ofNat 256 (2 ^ 110)),
    .arithmetic .add 1 6 1, .constant 7 2, .arithmetic .mul 7 0 7,
    .arithmetic .sub 1 1 7, .constant 3 (BitVec.ofNat 256 (2 ^ 110)), .arithmetic .add 3 1 3]

/-- The complete loader joins both fixed instruction lists. -/
def oracleLoad : List LinearInstruction := oracleLoadSetup ++ oracleLoadFinish

/-- The first loader block retains the computed header and saved scratch cells. -/
def oracleLoadInitial (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update (Function.update memory.registers
      1 (BitVec.ofNat 256 (2 ^ 128))) 6 (oracleHeader (memory.registers 9))) 15 13
    ram := oracleLoadRam memory }

/-- The source metadata uses the same used count for both transposition lists. -/
def oracleLoaded (memory : Memory) : Memory :=
  let header := oracleHeader (memory.registers 9)
  let saved := oracleLoadRam memory
  let used := saved header
  let input := header + BitVec.ofNat 256 (2 ^ 110) - used * 2#256
  { memory with
    registers := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        memory.registers 0 used) 1 input) 2 used) 3 (input + BitVec.ofNat 256 (2 ^ 110))) 4 used)
        5 (BitVec.ofNat 256 (2 ^ 128))) 6 header) 7 (used * 2#256)) 15 13
    ram := saved }

/-- The commit block persists the updated used count at the saved header address. -/
def oracleCommit : List LinearInstruction :=
  [.constant 15 13, .load 6 15, .store 6 0]

/-- The committed source changes only the used-count header and two temporary registers. -/
def oracleCommitted (memory : Memory) : Memory :=
  { memory with
    registers := Function.update (Function.update memory.registers 15 13) 6 (memory.ram 13)
    ram := Function.update memory.ram (memory.ram 13) (memory.registers 0) }

end Kriterion.ArgoMAC.ArithmeticSimulator
