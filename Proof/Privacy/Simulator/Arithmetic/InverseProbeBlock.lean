import Proof.Privacy.Simulator.Arithmetic.InverseProbe
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the inverse probe before its return instruction. -/
def ContainsInverseProbe (host : Machine) (labels : Fin 22 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 22, pc ≠ 21 → host.code[(labels pc).val] =
    relocate labels (inverseProbe.code[pc.val]'(by exact pc.isLt))

/-- The embedded probe contains the complete reverse scan. -/
theorem inverseProbeBlock_reverse (host : Machine)
    (labels : Fin 22 → Fin (host.size + 1)) (present : ContainsInverseProbe host labels) :
    ContainsReverseSwapTable host (labels ∘ inverseProbeLabels) := by
  intro pc valid
  have inside : inverseProbeLabels pc ≠ 21 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [inverseProbeLabels] at values
    omega
  have selected := present (inverseProbeLabels pc) inside
  have source := inverseProbe_reverse pc valid
  exact selected.trans ((congrArg (relocate labels) source).trans
    (relocate_comp inverseProbeLabels labels _))

/-- The host prepares the inverse scan in six instructions. -/
theorem inverseProbeBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 22 → Fin (host.size + 1)) (present : ContainsInverseProbe host labels)
    (memory : Memory) :
    runPrefix host 6 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 6, inverseProbeInitial memory⟩, 6)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), present 4 (by decide), present 5 (by decide),
    inverseProbe, relocate, inverseProbeInitial, executeLinear, inverseProbeSetup,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm, PMF.pure_map]

/-- The host writes the known-input flag in one instruction. -/
theorem inverseProbeBlock_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 22 → Fin (host.size + 1)) (present : ContainsInverseProbe host labels)
    (memory : Memory) :
    runPrefix host 1 ⟨labels 19, memory⟩ =
      PMF.pure (some (false, ⟨labels 21, inverseProbeFinal memory⟩, 1)) := by
  simp [runPrefix, step, present 19 (by decide), inverseProbe, relocate,
    inverseProbeFinal, PMF.pure_map]

/-- The full embedded probe returns the exact position, flag, and prefix cost. -/
theorem inverseProbeBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 22 → Fin (host.size + 1)) (present : ContainsInverseProbe host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 2 = BitVec.ofNat 256 count) :
    runPrefix host ((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 8)
      ⟨labels 0, memory⟩ =
      PMF.pure (some (false,
        ⟨labels 21, inverseProbeFinal (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).1⟩,
        (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 8)) := by
  rw [show (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 8 =
    6 + (((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 1) + 1) by omega,
    prefix_add, inverseProbeBlock_setup host labels present memory, PMF.pure_bind]
  dsimp only
  rw [prefix_add]
  have middle := reverseSwapBlock_prefix host (labels ∘ inverseProbeLabels)
    (inverseProbeBlock_reverse host labels present) count (inverseProbeInitial memory) fits
    (inverseProbe_counter count memory counter)
  change runPrefix host _ ⟨labels 6, inverseProbeInitial memory⟩ = _ at middle
  rw [middle, PMF.pure_bind]
  dsimp only
  change ((runPrefix host 1 ⟨labels 19, _⟩).map _).map _ = _
  rw [inverseProbeBlock_tail host labels present, PMF.pure_map, PMF.pure_map]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The inverse probe passes its complete memory and exact charge to the caller. -/
theorem inverseProbeBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 22 → Fin (host.size + 1)) (present : ContainsInverseProbe host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 2 = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 8 + fuel)
      ⟨labels 0, memory⟩ =
      (run host fuel
        ⟨labels 21, inverseProbeFinal (reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).1⟩).map
        (Option.map fun result => (result.1,
          result.2 + ((reverseSwapScan count (reverseSwapInitial (inverseProbeInitial memory))).2 + 8))) := by
  rw [run_after_prefix, inverseProbeBlock_prefix host labels present count memory fits counter,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
