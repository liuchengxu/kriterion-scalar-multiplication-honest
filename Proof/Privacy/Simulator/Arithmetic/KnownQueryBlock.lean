import Proof.Privacy.Simulator.Arithmetic.KnownQuery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the known-query path before its return instruction. -/
def ContainsKnownQuery (host : Machine) (labels : Fin 39 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 39, pc ≠ 38 → host.code[(labels pc).val] =
    relocate labels (knownQuery.code[pc.val]'(by exact pc.isLt))

/-- The host contains the complete inverse probe. -/
theorem knownQueryBlock_probe (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels) :
    ContainsInverseProbe host (labels ∘ knownProbeLabels) := by
  intro pc valid
  have inside : knownProbeLabels pc ≠ 38 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [knownProbeLabels] at values
    omega
  exact (present (knownProbeLabels pc) inside).trans
    ((congrArg (relocate labels) (knownQuery_probe pc valid)).trans
      (relocate_comp knownProbeLabels labels _))

/-- The host contains the complete forward scan. -/
theorem knownQueryBlock_swap (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels) :
    ContainsSwapTable host (labels ∘ knownSwapLabels) := by
  intro pc valid
  have inside : knownSwapLabels pc ≠ 38 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [knownSwapLabels] at values
    have different : pc.val ≠ 13 := by intro eq; apply valid; exact Fin.ext eq
    omega
  exact (present (knownSwapLabels pc) inside).trans
    ((congrArg (relocate labels) (knownQuery_swap pc valid)).trans
      (relocate_comp knownSwapLabels labels _))

/-- A fresh query returns to the caller in one instruction. -/
theorem knownQueryBlock_fresh [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels)
    (memory : Memory) (fresh : memory.registers 7 = 0#256) :
    runPrefix host 1 ⟨labels 21, memory⟩ =
      PMF.pure (some (false, ⟨labels 38, memory⟩, 1)) := by
  simp [runPrefix, step, present 21 (by decide), knownQuery, relocate, fresh, PMF.pure_map]

/-- A known query prepares the output scan in four instructions. -/
theorem knownQueryBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels)
    (memory : Memory) (known : memory.registers 7 ≠ 0#256) :
    runPrefix host 4 ⟨labels 21, memory⟩ =
      PMF.pure (some (false, ⟨labels 25, knownQueryInitial memory⟩, 4)) := by
  simp [runPrefix, step, present 21 (by decide), present 22 (by decide),
    present 23 (by decide), present 24 (by decide), knownQuery, relocate, known,
    knownQueryInitial, Arithmetic.eval, Function.update_comm, PMF.pure_map]

/-- The output branch returns its exact memory and cost to the caller. -/
theorem knownQueryBlock_branch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 4 = BitVec.ofNat 256 count) :
    runPrefix host ((knownQueryBranch count memory).2 - 1) ⟨labels 21, memory⟩ =
      PMF.pure (some (false, ⟨labels 38, (knownQueryBranch count memory).1⟩,
        (knownQueryBranch count memory).2 - 1)) := by
  by_cases fresh : memory.registers 7 = 0#256
  · simpa [knownQueryBranch, fresh] using knownQueryBlock_fresh host labels present memory fresh
  · simp only [knownQueryBranch, if_neg fresh]
    rw [show (swapScan count (swapInitial (knownQueryInitial memory))).2 + 5 - 1 =
      4 + (swapScan count (swapInitial (knownQueryInitial memory))).2 by omega,
      prefix_add, knownQueryBlock_setup host labels present memory fresh, PMF.pure_bind]
    have scan := swapBlock_prefix host (labels ∘ knownSwapLabels)
      (knownQueryBlock_swap host labels present) count (knownQueryInitial memory) fits
      (by simp [knownQueryInitial, counter])
    change runPrefix host _ ⟨labels 25, knownQueryInitial memory⟩ = _ at scan
    dsimp only
    rw [scan, PMF.pure_map]
    simp [knownSwapLabels, Function.comp_def, Nat.add_comm]

/-- The embedded query returns before its halt and retains the full state. -/
theorem knownQueryBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels)
    (inputCount outputCount : Nat) (memory : Memory)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    runPrefix host ((knownQueryScan inputCount outputCount memory).2 - 1) ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 38, (knownQueryScan inputCount outputCount memory).1⟩,
        (knownQueryScan inputCount outputCount memory).2 - 1)) := by
  let scanned := reverseSwapScan inputCount (reverseSwapInitial (inverseProbeInitial memory))
  let probed := inverseProbeFinal scanned.1
  have branchPositive : 1 ≤ (knownQueryBranch outputCount probed).2 := by
    unfold knownQueryBranch
    split <;> simp
  have order : (knownQueryScan inputCount outputCount memory).2 - 1 =
      (scanned.2 + 8) + ((knownQueryBranch outputCount probed).2 - 1) := by
    change (knownQueryBranch outputCount probed).2 + scanned.2 + 8 - 1 = _
    omega
  rw [order, prefix_add]
  have probe := inverseProbeBlock_prefix host (labels ∘ knownProbeLabels)
    (knownQueryBlock_probe host labels present) inputCount memory inputFits inputCounter
  change runPrefix host (scanned.2 + 8) ⟨labels 0, memory⟩ = _ at probe
  rw [probe, PMF.pure_bind]
  change (runPrefix host ((knownQueryBranch outputCount probed).2 - 1)
    ⟨labels 21, probed⟩).map _ = _
  rw [knownQueryBlock_branch host labels present outputCount probed outputFits
    (by simpa [probed, scanned, inverseProbe_outputCount] using outputCounter), PMF.pure_map]
  simp [knownQueryScan, scanned, probed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The embedded query retains unused fuel and charges every executed instruction. -/
theorem knownQueryBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 39 → Fin (host.size + 1)) (present : ContainsKnownQuery host labels)
    (inputCount outputCount : Nat) (memory : Memory)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) (fuel : Nat) :
    run host ((knownQueryScan inputCount outputCount memory).2 - 1 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 38, (knownQueryScan inputCount outputCount memory).1⟩).map
        (Option.map fun result => (result.1,
          result.2 + ((knownQueryScan inputCount outputCount memory).2 - 1))) := by
  rw [run_after_prefix, knownQueryBlock_prefix host labels present inputCount outputCount memory
    inputFits outputFits inputCounter outputCounter, PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
