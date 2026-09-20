import Construction.Simulator.InverseProbe
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Proof.Privacy.Simulator.Arithmetic.ReverseSwapBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The probe contains the exact six-instruction setup. -/
theorem inverseProbe_setup : ContainsLinear inverseProbe inverseProbeSetup
    (fun index => ⟨min index 6, by change min index 6 < 22; omega⟩) := by
  intro index valid
  have bound : index < 6 := valid
  interval_cases index <;> simp [inverseProbe, inverseProbeSetup, LinearInstruction.emit]

/-- The probe contains the complete reverse scan before the flag instruction. -/
theorem inverseProbe_reverse : ContainsReverseSwapTable inverseProbe inverseProbeLabels := by
  intro pc valid
  fin_cases pc <;> simp_all [inverseProbe, inverseProbeLabels, reverseSwapTable, relocate]

/-- The setup prepares the last RAM pair and preserves the query and used count. -/
def inverseProbeInitial (memory : Memory) : Memory := executeLinear inverseProbeSetup memory

/-- The final instruction compares the inverse position with the used count. -/
def inverseProbeFinal (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 7 (Arithmetic.less.eval (memory.registers 8) (memory.registers 0)) }

/-- The probe's final comparison and halt use two instructions. -/
theorem inverseProbe_tail [BN254.FieldCertificate] (memory : Memory) :
    run inverseProbe 2 ⟨19, memory⟩ = PMF.pure (some (⟨21, inverseProbeFinal memory⟩, 2)) := by
  simp [run, step, inverseProbe, inverseProbeFinal, PMF.pure_map]
  rfl

/-- The source count remains available after setup. -/
theorem inverseProbe_counter (count : Nat) (memory : Memory)
    (counter : memory.registers 2 = BitVec.ofNat 256 count) :
    (inverseProbeInitial memory).registers 10 = BitVec.ofNat 256 count := by
  simp [inverseProbeInitial, executeLinear, inverseProbeSetup, LinearInstruction.execute,
    Arithmetic.eval, counter]

/-- The probe computes the complete inverse scan before it returns the known-input flag. -/
theorem inverseProbe_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 2 = BitVec.ofNat 256 count) :
    let scanned := reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))
    run inverseProbe (scanned.2 + 9) ⟨0, memory⟩ =
      PMF.pure (some (⟨21, inverseProbeFinal scanned.1⟩, scanned.2 + 9)) := by
  dsimp only
  have continuation := reverseSwapBlock_continue inverseProbe inverseProbeLabels
    inverseProbe_reverse count (inverseProbeInitial memory) fits
    (inverseProbe_counter count memory counter) 2
  have prepared : runPrefix inverseProbe 6 ⟨0, memory⟩ =
      PMF.pure (some (false, ⟨6, inverseProbeInitial memory⟩, 6)) := by
    simp [runPrefix, step, inverseProbe, inverseProbeInitial, executeLinear, inverseProbeSetup,
      LinearInstruction.execute, Arithmetic.eval, Function.update_comm, PMF.pure_map]
    rfl
  rw [show (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 9 =
    6 + ((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 1 + 2) by omega,
    run_after_prefix, prepared, PMF.pure_bind]
  dsimp only
  change (run inverseProbe _ ⟨inverseProbeLabels 0, inverseProbeInitial memory⟩).map _ = _
  rw [continuation]
  change ((run inverseProbe 2 ⟨19, _⟩).map _).map _ = _
  rw [inverseProbe_tail, PMF.pure_map, PMF.pure_map]
  simp only [Option.map_some]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The complete probe costs at most eleven units per pair plus thirty-three. -/
theorem inverseProbe_budget (count : Nat) (memory : Memory) :
    inverseProbe.size + 1 +
      ((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 9) ≤
      11 * count + 33 := by
  have bound := (reverseSwapScan_cost count (reverseSwapInitial (inverseProbeInitial memory))).2
  change 21 + 1 + (_ + 9) ≤ _
  omega

/-- The reverse scan preserves each register below eight. -/
theorem reverseSwapScan_caller (count : Nat) (memory : Memory) (register : Register)
    (low : register.val < 8) :
    (reverseSwapScan count memory).1.registers register = memory.registers register := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      change (reverseSwapScan count (reverseSwapMemory memory)).1.registers register = _
      rw [ih]
      fin_cases register <;> simp_all [reverseSwapMemory]

/-- The probe's output equals the inverse position and its known-input test. -/
theorem inverseProbe_source [BN254.FieldCertificate]
    (pairs : List (Word × Word)) (memory : Memory) (fits : pairs.length < 2 ^ 256)
    (counter : memory.registers 2 = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (memory.registers 1) pairs) :
    let position := (Security.OperationalOracle.swaps pairs).symm (memory.registers 8)
    (run inverseProbe
      ((reverseSwapScan pairs.length (reverseSwapInitial (inverseProbeInitial memory))).2 + 9)
      ⟨0, memory⟩).map
      (Option.map fun result => (result.1.memory.registers 8, result.1.memory.registers 7)) =
      PMF.pure (some (position,
        if position.toNat < (memory.registers 0).toNat then 1#256 else 0#256)) := by
  dsimp only
  have source := applyReverseTableSwaps_inverse pairs memory.ram
    (memory.registers 1) (memory.registers 8) represented
  have position : (reverseSwapScan pairs.length
      (reverseSwapInitial (inverseProbeInitial memory))).1.registers 8 =
      (Security.OperationalOracle.swaps pairs).symm (memory.registers 8) := by
    rw [reverseSwapScan_source]
    simpa [reverseSwapInitial, inverseProbeInitial, executeLinear, inverseProbeSetup,
      LinearInstruction.execute, Arithmetic.eval, counter, BitVec.ofNat_mul, Nat.mul_comm, mul_comm] using source
  have used : (reverseSwapScan pairs.length
      (reverseSwapInitial (inverseProbeInitial memory))).1.registers 0 = memory.registers 0 := by
    rw [reverseSwapScan_caller _ _ 0 (by decide)]
    simp [reverseSwapInitial, inverseProbeInitial, executeLinear, inverseProbeSetup,
      LinearInstruction.execute]
  rw [inverseProbe_run pairs.length memory fits counter, PMF.pure_map]
  simp [inverseProbeFinal, Arithmetic.eval, position, used]

end Kriterion.ArgoMAC.ArithmeticSimulator
