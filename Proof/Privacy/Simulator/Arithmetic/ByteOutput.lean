import Construction.Simulator.ByteOutput
import Proof.Privacy.Simulator.Arithmetic.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The RAM loop contains the fixed eight-bit output program. -/
theorem byteOutput_contains : ContainsLinear byteOutput (wordOutput 8) byteOutputLabels := by
  intro index valid
  have small : index < 24 := valid
  simp [byteOutput, byteOutputLabels, small, show ¬ index + 5 < 5 by omega,
    show index + 5 < 29 by omega]

/-- The bit output preserves every register except its two temporary registers. -/
theorem wordOutput_saved (width : Nat) (memory : Memory) (register : Register)
    (first : register ≠ 9) (second : register ≠ 10) :
    (executeLinear (wordOutput width) memory).registers register = memory.registers register := by
  induction width generalizing memory with
  | zero => rfl
  | succ width ih =>
      simp only [wordOutput, executeLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (executeLinear (wordOutput width) _).registers register = _
      rw [ih]
      simp [LinearInstruction.execute, first, second]

/-- The loop loads the last remaining RAM byte. -/
def bytePrepared (count : Nat) (memory : Memory) : Memory :=
  let address := memory.registers 11 + BitVec.ofNat 256 count
  { memory with
    registers := Function.update (Function.update
      (Function.update memory.registers 12 (BitVec.ofNat 256 count)) 14 address) 8 (memory.ram address) }

def byteWritten (count : Nat) (memory : Memory) : Memory :=
  executeLinear (wordOutput 8) (bytePrepared count memory)

/-- The preparation charges its branch, decrement, address sum, and RAM read. -/
theorem byteOutput_prepare [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count + 1 < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 (count + 1))
    (one : memory.registers 13 = 1#256) :
    runPrefix byteOutput 4 ⟨1, memory⟩ =
      PMF.pure (some (false, ⟨5, bytePrepared count memory⟩, 4)) := by
  have nonzero : memory.registers 12 ≠ 0#256 := by
    rw [counter]
    intro equal
    have values := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at values
    change count + 1 = 0 at values
    omega
  rw [counter] at nonzero
  have decrement : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
    rw [BitVec.ofNat_add]
    simp
  simp [runPrefix, step, byteOutput, nonzero, counter, one, decrement, bytePrepared,
    Arithmetic.eval, PMF.pure_map]
  rfl

/-- The RAM loop writes one byte in exactly twenty-eight instructions. -/
theorem byteOutput_step [BN254.FieldCertificate] (count fuel : Nat) (memory : Memory)
    (fits : count + 1 < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 (count + 1))
    (one : memory.registers 13 = 1#256) :
    runPrefix byteOutput (fuel + 28) ⟨1, memory⟩ =
      (runPrefix byteOutput fuel ⟨1, byteWritten count memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 28)) := by
  have output := linear_prefix byteOutput (wordOutput 8) byteOutputLabels
    byteOutput_contains (bytePrepared count memory)
  change runPrefix byteOutput 24 ⟨5, bytePrepared count memory⟩ =
    PMF.pure (some (false, ⟨1, byteWritten count memory⟩, 24)) at output
  rw [show fuel + 28 = 4 + (24 + fuel) by omega, prefix_add,
    byteOutput_prepare count memory fits counter one, PMF.pure_bind]
  dsimp only
  rw [prefix_add, output, PMF.pure_bind]
  dsimp only
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- Each byte write preserves RAM and the loop registers. -/
theorem byteWritten_state (count : Nat) (memory : Memory) :
    (byteWritten count memory).ram = memory.ram ∧
    (byteWritten count memory).registers 11 = memory.registers 11 ∧
    (byteWritten count memory).registers 12 = BitVec.ofNat 256 count ∧
    (byteWritten count memory).registers 13 = memory.registers 13 := by
  simp [byteWritten, wordOutput_ram, wordOutput_saved, bytePrepared]

/-- A byte write prepends its canonical eight bits to the previous output. -/
theorem byteWritten_bits (count : Nat) (memory : Memory) :
    (byteWritten count memory).bits 3 =
      GarbledCircuit.SimulatorProtocol.bits 8
        (memory.ram (memory.registers 11 + BitVec.ofNat 256 count)).toNat ++ memory.bits 3 := by
  unfold byteWritten
  rw [wordOutput_bits 8 _ (by decide)]
  simp [bytePrepared, wordOutput_protocol]

/-- The source scan writes the last byte first. -/
def byteScan : Nat → Memory → Memory
  | 0, memory => memory
  | count + 1, memory => byteScan count (byteWritten count memory)

/-- The complete loop returns before its final halt. -/
theorem byteOutput_loop [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 12 = BitVec.ofNat 256 count)
    (one : memory.registers 13 = 1#256) :
    runPrefix byteOutput (28 * count + 1) ⟨1, memory⟩ =
      PMF.pure (some (false, ⟨29, byteScan count memory⟩, 28 * count + 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [runPrefix, step, byteOutput, counter, byteScan, PMF.pure_map]
      rfl
  | succ count ih =>
      rw [show 28 * (count + 1) + 1 = (28 * count + 1) + 28 by omega,
        byteOutput_step count (28 * count + 1) memory fits counter one,
        ih (byteWritten count memory) (by omega) (byteWritten_state count memory).2.2.1
          ((byteWritten_state count memory).2.2.2.trans one)]
      simp [byteScan, PMF.pure_map, Nat.add_assoc]

def byteInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 13 1 }

/-- The machine charges its entry and final halt as well as each byte. -/
theorem byteOutput_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 12 = BitVec.ofNat 256 count) :
    run byteOutput (28 * count + 3) ⟨0, memory⟩ =
      PMF.pure (some (⟨29, byteScan count (byteInitial memory)⟩, 28 * count + 3)) := by
  have setup (fuel : Nat) : run byteOutput (fuel + 1) ⟨0, memory⟩ =
      (run byteOutput fuel ⟨1, byteInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
    simp [run, step, byteOutput, byteInitial]
    rfl
  rw [show 28 * count + 3 = (28 * count + 2) + 1 by omega, setup]
  have loop := byteOutput_loop count (byteInitial memory) fits
    (by simpa [byteInitial] using counter) (by simp [byteInitial])
  have continued := run_after_prefix byteOutput (28 * count + 1) 1 ⟨1, byteInitial memory⟩
  rw [loop, PMF.pure_bind] at continued
  rw [show 28 * count + 2 = (28 * count + 1) + 1 by omega, continued]
  simp [run, step, byteOutput, PMF.pure_map, Nat.add_assoc, Nat.add_comm]

/-- The output order matches the original ascending RAM addresses. -/
theorem byteScan_bits (count : Nat) (memory : Memory) :
    (byteScan count memory).bits 3 =
      (List.range count).flatMap (fun index => GarbledCircuit.SimulatorProtocol.bits 8
        (memory.ram (memory.registers 11 + BitVec.ofNat 256 index)).toNat) ++ memory.bits 3 := by
  induction count generalizing memory with
  | zero => simp [byteScan]
  | succ count ih =>
      rw [byteScan, ih]
      simp only [(byteWritten_state count memory).1, (byteWritten_state count memory).2.1,
        byteWritten_bits, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc]

/-- The closed machine returns the canonical bit sequence for the stored bytes. -/
theorem byteOutput_source [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 12 = BitVec.ofNat 256 count) :
    (run byteOutput (28 * count + 3) ⟨0, memory⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.2)) =
      PMF.pure (some ((List.range count).flatMap (fun index =>
        GarbledCircuit.SimulatorProtocol.bits 8
          (memory.ram (memory.registers 11 + BitVec.ofNat 256 index)).toNat) ++ memory.bits 3,
        28 * count + 3)) := by
  rw [byteOutput_run count memory fits counter, PMF.pure_map]
  simp [byteScan_bits, byteInitial]

/-- The total byte-output budget includes all thirty table entries. -/
theorem byteOutput_budget (count : Nat) :
    byteOutput.size + 1 + (28 * count + 3) = 28 * count + 33 := by
  change 29 + 1 + (28 * count + 3) = _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
