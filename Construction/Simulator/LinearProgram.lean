import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A linear instruction has fixed operands and one continuation. -/
inductive LinearInstruction
  | constant (target : Register) (value : Word)
  | arithmetic (operation : Arithmetic) (target left right : Register)
  | load (target address : Register)
  | store (address source : Register)
  | push (stack : Fin 4) (bit : Bool)
  | pushBit (stack : Fin 4) (source : Register)

/-- The assembler adds the continuation label to each instruction. -/
def LinearInstruction.emit {labels : Nat} (next : Fin labels) :
    LinearInstruction → Instruction labels
  | .constant target value => .constant target value next
  | .arithmetic operation target left right => .arithmetic operation target left right next
  | .load target address => .load target address next
  | .store address source => .store address source next
  | .push stack bit => .push stack bit next
  | .pushBit stack source => .pushBit stack source next

/-- The source semantics use the same fixed arithmetic and memory operations. -/
def LinearInstruction.execute (instruction : LinearInstruction) (memory : Memory) : Memory :=
  match instruction with
  | .constant target value =>
      { memory with registers := Function.update memory.registers target value }
  | .arithmetic operation target left right =>
      { memory with registers := Function.update memory.registers target (operation.eval (memory.registers left) (memory.registers right)) }
  | .load target address =>
      { memory with registers := Function.update memory.registers target (memory.ram (memory.registers address)) }
  | .store address source =>
      { memory with ram := Function.update memory.ram (memory.registers address) (memory.registers source) }
  | .push stack bit =>
      { memory with bits := Function.update memory.bits stack (bit :: memory.bits stack) }
  | .pushBit stack source =>
      { memory with bits := Function.update memory.bits stack ((memory.registers source).getLsbD 0 :: memory.bits stack) }

/-- A linear program applies its instructions in list order. -/
def executeLinear (program : List LinearInstruction) (memory : Memory) : Memory :=
  program.foldl (fun state instruction => instruction.execute state) memory

/-- The compiler emits one machine instruction per source instruction and one halt. -/
def linearMachine (program : List LinearInstruction) (fits : program.length < 2 ^ 256) : Machine :=
  ⟨program.length, Vector.ofFn (fun pc =>
    if valid : pc.val < program.length then
      (program[pc.val]).emit ⟨pc.val + 1, by omega⟩
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
