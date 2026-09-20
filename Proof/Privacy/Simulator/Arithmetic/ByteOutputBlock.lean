import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.ByteOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host supplies the byte loop and chooses its return instruction. -/
def ContainsByteOutput (host : Machine) (labels : Fin 30 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 30, pc.val < 29 → host.code[(labels pc).val] =
    relocate labels (byteOutput.code[pc.val]'(by exact pc.isLt))

/-- Relocation preserves each linear instruction and changes its continuation. -/
theorem LinearInstruction.relocate_emit {source target : Nat}
    (labels : Fin source → Fin target) (next : Fin source) (instruction : LinearInstruction) :
    relocate labels (instruction.emit next) = instruction.emit (labels next) := by
  cases instruction <;> rfl

/-- The host contains the inner eight-bit output block. -/
theorem byteOutputBlock_contains (host : Machine) (labels : Fin 30 → Fin (host.size + 1))
    (present : ContainsByteOutput host labels) :
    ContainsLinear host (wordOutput 8) (fun index => labels (byteOutputLabels index)) := by
  intro index valid
  have small : index < 24 := valid
  have pc : (byteOutputLabels index).val < 29 := by simp [byteOutputLabels, small]; omega
  exact (present _ pc).trans ((congrArg (relocate labels)
    (byteOutput_contains index valid)).trans (LinearInstruction.relocate_emit labels _ _))

theorem byteOutputBlock_prepare [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 30 → Fin (host.size + 1)) (present : ContainsByteOutput host labels) (count : Nat) (memory : Memory)
    (fits : count + 1 < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 (count + 1))
    (one : memory.registers 13 = 1#256) :
    runPrefix host 4 ⟨labels 1, memory⟩ =
      PMF.pure (some (false, ⟨labels 5, bytePrepared count memory⟩, 4)) := by
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
  simp [runPrefix, step, present 1 (by decide), present 2 (by decide),
    present 3 (by decide), present 4 (by decide), relocate, byteOutput, nonzero, counter, one, decrement, bytePrepared,
    Arithmetic.eval, PMF.pure_map]


theorem byteOutputBlock_step [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 30 → Fin (host.size + 1)) (present : ContainsByteOutput host labels) (count fuel : Nat) (memory : Memory)
    (fits : count + 1 < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 (count + 1))
    (one : memory.registers 13 = 1#256) :
    runPrefix host (fuel + 28) ⟨labels 1, memory⟩ =
      (runPrefix host fuel ⟨labels 1, byteWritten count memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 28)) := by
  have output := linear_prefix host (wordOutput 8) (fun index => labels (byteOutputLabels index))
    (byteOutputBlock_contains host labels present) (bytePrepared count memory)
  change runPrefix host 24 ⟨labels 5, bytePrepared count memory⟩ =
    PMF.pure (some (false, ⟨labels 1, byteWritten count memory⟩, 24)) at output
  rw [show fuel + 28 = 4 + (24 + fuel) by omega, prefix_add,
    byteOutputBlock_prepare host labels present count memory fits counter one, PMF.pure_bind]
  dsimp only
  rw [prefix_add, output, PMF.pure_bind]
  dsimp only
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]


theorem byteOutputBlock_loop [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 30 → Fin (host.size + 1)) (present : ContainsByteOutput host labels) (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 12 = BitVec.ofNat 256 count)
    (one : memory.registers 13 = 1#256) :
    runPrefix host (28 * count + 1) ⟨labels 1, memory⟩ =
      PMF.pure (some (false, ⟨labels 29, byteScan count memory⟩, 28 * count + 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [runPrefix, step, present 1 (by decide), relocate, byteOutput, counter, byteScan, PMF.pure_map]
  | succ count ih =>
      rw [show 28 * (count + 1) + 1 = (28 * count + 1) + 28 by omega,
        byteOutputBlock_step host labels present count (28 * count + 1) memory fits counter one,
        ih (byteWritten count memory) (by omega) (byteWritten_state count memory).2.2.1
          ((byteWritten_state count memory).2.2.2.trans one)]
      simp [byteScan, PMF.pure_map, Nat.add_assoc]

/-- The host initializes the byte loop and returns before its continuation. -/
theorem byteOutputBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 30 → Fin (host.size + 1)) (present : ContainsByteOutput host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 count) :
    runPrefix host (28 * count + 2) ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 29, byteScan count (byteInitial memory)⟩,
        28 * count + 2)) := by
  have setup (fuel : Nat) : runPrefix host (fuel + 1) ⟨labels 0, memory⟩ =
      (runPrefix host fuel ⟨labels 1, byteInitial memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
    simp [runPrefix, step, present 0 (by decide), byteOutput, relocate, byteInitial]
  rw [show 28 * count + 2 = (28 * count + 1) + 1 by omega, setup,
    byteOutputBlock_loop host labels present count (byteInitial memory) fits
      (by simpa [byteInitial] using counter) (by simp [byteInitial]), PMF.pure_map]
  rfl

/-- The caller resumes with the complete memory and exact output cost. -/
theorem byteOutputBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 30 → Fin (host.size + 1)) (present : ContainsByteOutput host labels)
    (count fuel : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 12 = BitVec.ofNat 256 count) :
    run host (28 * count + 2 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 29, byteScan count (byteInitial memory)⟩).map
        (Option.map fun result => (result.1, result.2 + (28 * count + 2))) := by
  rw [run_after_prefix, byteOutputBlock_prefix host labels present count memory fits counter,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
