import Construction.Simulator.OracleMetadata
import Construction.Simulator.PairStore
import Construction.Simulator.TableLookup
import Construction.Simulator.WordSampler
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The hash setup retains the table base across the uniform reply sampler. -/
def hashSetup : List LinearInstruction :=
  [.constant 6 0, .arithmetic .add 5 1 6, .arithmetic .add 9 1 6, .arithmetic .add 10 0 6]

def hashReady (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update memory.registers 6 0) 5 (memory.registers 1))
      9 (memory.registers 1)) 10 (memory.registers 0) }

/-- A fresh hash reply prepends one key-value pair and updates the table count. -/
def hashInstall : List LinearInstruction :=
  [.constant 6 0, .arithmetic .add 13 0 6, .constant 14 2,
    .arithmetic .sub 9 5 14, .arithmetic .add 10 0 6] ++ pairStore ++
  [.arithmetic .add 1 9 6, .arithmetic .add 0 4 14, .arithmetic .add 4 0 6,
    .arithmetic .add 2 0 6, .arithmetic .add 8 13 6, .constant 7 1]

def hashInstalled (memory : Memory) : Memory :=
  let address := memory.registers 5 - 2#256
  let count := memory.registers 4 + 1#256
  { memory with
    registers := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update memory.registers 6 0) 13 (memory.registers 0)) 14 1)
      9 address) 10 (memory.registers 0)) 1 address) 0 count) 4 count) 2 count)
      8 (memory.registers 0)) 7 1
    ram := Function.update (Function.update memory.ram address (memory.registers 8))
      (address + 1#256) (memory.registers 0) }

/-- A known hash reply returns its stored value with a success flag. -/
def hashKnown : List LinearInstruction :=
  [.constant 6 0, .arithmetic .add 8 11 6, .constant 7 1]

def hashFound (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      memory.registers 6 0) 8 (memory.registers 11)) 7 1 }

/-- The insertion returns directly to the commit and skips the known-answer branch. -/
def hashInstallLabels (index : Nat) : Fin 74 :=
  if inside : index < 16 then ⟨51 + index, by omega⟩ else 70

/-- The complete hash handler uses exact 256-bit sampling and a first-match sparse table. -/
def hashHandler : Machine := ⟨73, Vector.ofFn (fun pc =>
  if load : pc.val < 22 then
    (oracleLoad[pc.val]'(by change pc.val < 22; exact load)).emit ⟨pc.val + 1, by omega⟩
  else if setup : 22 ≤ pc.val ∧ pc.val < 26 then
    (hashSetup[pc.val - 22]'(by change pc.val - 22 < 4; omega)).emit ⟨pc.val + 1, by omega⟩
  else if lookup : 26 ≤ pc.val ∧ pc.val < 39 ∧ pc.val ≠ 35 then
    relocate (fun label : Fin 13 => (⟨label.val + 26, by omega⟩ : Fin 74))
      (tableLookup.code[pc.val - 26]'(by change pc.val - 26 < 13; omega))
  else if sample : 39 ≤ pc.val ∧ pc.val < 51 then
    relocate (fun label : Fin 13 => (⟨label.val + 39, by omega⟩ : Fin 74))
      ((wordSampler 256).code[pc.val - 39]'(by change pc.val - 39 < 13; omega))
  else if install : 51 ≤ pc.val ∧ pc.val < 67 then
    (hashInstall[pc.val - 51]'(by change pc.val - 51 < 16; omega)).emit
      (hashInstallLabels (pc.val - 51 + 1))
  else if known : 67 ≤ pc.val ∧ pc.val < 70 then
    (hashKnown[pc.val - 67]'(by change pc.val - 67 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if commit : 70 ≤ pc.val ∧ pc.val < 73 then
    (oracleCommit[pc.val - 70]'(by change pc.val - 70 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if pc.val = 35 then .branch 12 39 67 else .halt), by decide⟩

def hashLoadLabels (index : Nat) : Fin 74 := ⟨min index 22, by omega⟩
def hashSetupLabels (index : Nat) : Fin 74 := ⟨22 + min index 4, by omega⟩
def hashTableLabels (pc : Fin 13) : Fin 74 := ⟨pc.val + 26, by omega⟩
def hashWordLabels (pc : Fin 13) : Fin 74 := ⟨pc.val + 39, by omega⟩
def hashKnownLabels (index : Nat) : Fin 74 := ⟨67 + min index 3, by omega⟩
def hashCommitLabels (index : Nat) : Fin 74 := ⟨70 + min index 3, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
