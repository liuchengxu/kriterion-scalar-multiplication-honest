import Construction.Simulator.HashHandler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The target load reads the packed programmed hash value from scratch cell fourteen. -/
def hashProgramTarget : List LinearInstruction := [.constant 15 14, .load 0 15]

/-- The target source preserves the selected hash input in register eight. -/
def hashProgramTargetMemory (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update memory.registers 15 14) 0 (memory.ram 14) }

/-- The hash programming block prepends the target value and commits the increased count. -/
def hashProgram : List LinearInstruction :=
  oracleLoad ++ hashSetup ++ hashProgramTarget ++ hashInstall ++ oracleCommit

/-- The source retains the same first-match override rule as the operational hash table. -/
def hashProgrammed (memory : Memory) : Memory :=
  oracleCommitted (hashInstalled (hashProgramTargetMemory (hashReady (oracleLoaded memory))))

end Kriterion.ArgoMAC.ArithmeticSimulator
