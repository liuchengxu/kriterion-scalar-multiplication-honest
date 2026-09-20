import Construction.Simulator.BoundedSampler
import Proof.Privacy.Simulator.Arithmetic.TrialMemory
import Proof.Privacy.ThreePhasePrivacy

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The retry program contains the trial before its flag branch. -/
theorem boundedSampler_contains (size attempts : Nat) :
    ContainsTrial (boundedSampler size attempts) (min (size.log2 + 1) 256)
      (BitVec.ofNat 256 size) (size == 2 ^ 256) retryLabels := by
  intro pc inside
  have positive : 0 < pc.val + 1 := by omega
  have upper : pc.val + 1 < 20 := by omega
  simp [boundedSampler, retryLabels, boundedTrial, upper]
  split
  · rfl
  · rename_i impossible
    exact (impossible (by change 0 < pc.val + 1; exact positive)).elim

/-- This count reserves one trial and two control instructions for each allowed attempt. -/
def retryFuel (size attempts : Nat) : Nat := (trialCost size + 2) * attempts + 3

/-- This law records the first accepted trial or the exhausted retry limit. -/
noncomputable def retryLaw (size : Nat) : Nat → PMF (Option Word × Nat)
  | 0 => PMF.pure (none, 3)
  | count + 1 => ((Security.BoundedIntegerSampling.trial size).map
      (Option.map fun value => BitVec.ofNat 256 value.val)).bind fun value =>
      match value with
      | none => (retryLaw size count).map fun result => (result.1, result.2 + trialCost size + 2)
      | some accepted => PMF.pure (some accepted, trialCost size + 2)

/-- The exhausted loop clears its acceptance flag and halts. -/
theorem boundedSampler_zero [BN254.FieldCertificate] (size attempts fuel : Nat) (base : Memory)
    (empty : base.registers 4 = 0) :
    run (boundedSampler size attempts) (fuel + 3) ⟨22, base⟩ =
      PMF.pure (some (⟨24, {base with registers := Function.update base.registers 7 0}⟩, 3)) := by
  simp [run, step, boundedSampler, empty, PMF.pure_map]
  rfl

/-- A successful trial reaches the halt in two control instructions. -/
theorem boundedSampler_accept [BN254.FieldCertificate] (size attempts fuel : Nat) (base : Memory)
    (accepted : base.registers 7 ≠ 0) :
    run (boundedSampler size attempts) (fuel + 2) ⟨20, base⟩ =
      PMF.pure (some (⟨24, base⟩, 2)) := by
  change base.registers 7 ≠ 0#256 at accepted
  simp [run, step, boundedSampler, accepted, PMF.pure_map]
  rfl

/-- A rejected trial decrements the retry counter and returns to the loop guard. -/
theorem boundedSampler_reject [BN254.FieldCertificate] (size attempts fuel : Nat) (base : Memory)
    (rejected : base.registers 7 = 0) (one : base.registers 1 = 1) :
    run (boundedSampler size attempts) (fuel + 2) ⟨20, base⟩ =
      (run (boundedSampler size attempts) fuel
        ⟨22, {base with registers := Function.update base.registers 4 (base.registers 4 - 1)}⟩).map
          (Option.map fun result => (result.1, result.2 + 2)) := by
  simp [run, step, boundedSampler, rejected, one, Arithmetic.eval,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

/-- The guard and the trial pass memory and cost to the result branch. -/
theorem boundedSampler_trial [BN254.FieldCertificate] (size attempts fuel : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (nonzero : base.registers 4 ≠ 0#256) :
    run (boundedSampler size attempts) (trialCost size + fuel) ⟨22, base⟩ =
      (trialMemory size base).bind fun memory =>
        (run (boundedSampler size attempts) fuel ⟨20, memory⟩).map
          (Option.map fun result => (result.1, result.2 + trialCost size)) := by
  have costPositive : 1 ≤ trialCost size := by unfold trialCost; split <;> omega
  have guard : step (boundedSampler size attempts) ⟨22, base⟩ =
      PMF.pure (some (false, ⟨retryLabels 0, base⟩)) := by
    simp [step, boundedSampler, nonzero, retryLabels]
  have continued := run_after_prefix (boundedSampler size attempts) (trialCost size - 1) fuel
    ⟨retryLabels 0, base⟩
  have block := boundedTrial_block (boundedSampler size attempts) size retryLabels
    (boundedSampler_contains size attempts) base positive bounded
  rw [block] at continued
  rw [show trialCost size + fuel = (trialCost size - 1 + fuel) + 1 by omega,
    run, guard, PMF.pure_bind]
  change (run (boundedSampler size attempts) (trialCost size - 1 + fuel)
    ⟨retryLabels 0, base⟩).map (Option.map fun result => (result.1, result.2 + 1)) = _
  rw [continued]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.map_comp]
  apply congrArg (PMF.bind (trialMemory size base))
  funext memory
  change (run (boundedSampler size attempts) fuel ⟨20, memory⟩).map _ = _
  apply congrArg (fun f => PMF.map f (run (boundedSampler size attempts) fuel ⟨20, memory⟩))
  funext result
  cases result <;> simp [Nat.add_assoc, Nat.sub_add_cancel costPositive]

/-- The source retry law can use the verified trial memory. -/
theorem retryLaw_memory [BN254.FieldCertificate] (size count : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    retryLaw size (count + 1) = (trialMemory size base).bind fun memory =>
      match trialValue memory with
      | none => (retryLaw size count).map fun result => (result.1, result.2 + trialCost size + 2)
      | some value => PMF.pure (some value, trialCost size + 2) := by
  rw [retryLaw, ← trialMemory_source size base positive bounded, PMF.bind_map]
  rfl

/-- The complete retry loop follows the source trials and retains its actual cost. -/
theorem boundedSampler_loop [BN254.FieldCertificate] (size attempts count : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : count < 2 ^ 256)
    (counter : base.registers 4 = BitVec.ofNat 256 count) :
    (run (boundedSampler size attempts) (retryFuel size count) ⟨22, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (retryLaw size count).map some := by
  induction count generalizing base with
  | zero =>
      have empty : base.registers 4 = 0 := by simpa using counter
      rw [show retryFuel size 0 = 0 + 3 from rfl, boundedSampler_zero size attempts 0 base empty]
      simp [PMF.pure_map, trialValue, retryLaw]
  | succ count ih =>
      have nonzero : base.registers 4 ≠ 0#256 := by
        rw [counter]
        intro equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countFits] at natural
        change count + 1 = 0 at natural
        omega
      have fuel : retryFuel size (count + 1) = trialCost size + (retryFuel size count + 2) := by
        unfold retryFuel
        ring
      rw [fuel, boundedSampler_trial size attempts (retryFuel size count + 2) base positive bounded nonzero,
        PMF.map_bind, retryLaw_memory size count base positive bounded, PMF.map_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro memory supported
      obtain ⟨same, one⟩ := trialMemory_registers size base memory supported
      by_cases rejected : memory.registers 7 = 0
      · rw [boundedSampler_reject size attempts (retryFuel size count) memory rejected one]
        let next : Memory :=
          {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}
        have nextCounter : next.registers 4 = BitVec.ofNat 256 count := by
          simp only [next, Function.update_self]
          rw [same, counter, BitVec.ofNat_add]
          simp
        have previous := ih next (by omega) nextCounter
        have projected := congrArg
          (PMF.map (Option.map fun result : Option Word × Nat =>
            (result.1, result.2 + 2 + trialCost size))) previous
        simp only [trialValue, rejected, ite_true] at ⊢
        simpa only [next, trialValue, PMF.map_comp, Function.comp_def, Option.map_map, Option.map_some,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using projected
      · rw [boundedSampler_accept size attempts (retryFuel size count) memory rejected]
        change memory.registers 7 ≠ 0#256 at rejected
        simp [PMF.pure_map, trialValue, rejected, Nat.add_comm]

/-- The retry law returns the same accepted word as the source cutoff. -/
theorem retryLaw_source (size count : Nat) :
    (retryLaw size count).map Prod.fst =
      (Security.BoundedIntegerSampling.cutoff size count).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  induction count with
  | zero => simp [retryLaw, Security.BoundedIntegerSampling.cutoff,
      Security.BoundedIntegerSampling.BitCode.law, PMF.pure_map]
  | succ count ih =>
      rw [retryLaw, PMF.map_bind, PMF.bind_map,
        Security.BoundedIntegerSampling.cutoff_succ_law, PMF.map_bind]
      apply congrArg (PMF.bind (Security.BoundedIntegerSampling.trial size))
      funext value
      cases value with
      | none =>
          simp only [Function.comp_def, Option.map_none, PMF.map_comp]
          exact ih
      | some value => simp [Function.comp_def, PMF.pure_map]

/-- The entry instruction initializes the counter before the verified retry loop. -/
theorem boundedSampler_run [BN254.FieldCertificate] (size attempts : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    (run (boundedSampler size attempts) (retryFuel size attempts + 1) ⟨0, base⟩).map
      (Option.map fun result => (trialValue result.1.memory, result.2)) =
        (retryLaw size attempts).map fun result => some (result.1, result.2 + 1) := by
  let initialized : Memory := {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}
  have entry : step (boundedSampler size attempts) ⟨0, base⟩ =
      PMF.pure (some (false, ⟨22, initialized⟩)) := by
    simp [step, boundedSampler, initialized]
    rfl
  have loop := boundedSampler_loop size attempts attempts initialized positive bounded countFits
    (by simp [initialized])
  have projected := congrArg
    (PMF.map (Option.map fun result : Option Word × Nat => (result.1, result.2 + 1))) loop
  rw [run, entry, PMF.pure_bind]
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map, Option.map_some] using projected

/-- The closed sampler matches the source cutoff, including its failure outcome. -/
theorem boundedSampler_source [BN254.FieldCertificate] (size attempts : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    (run (boundedSampler size attempts) (retryFuel size attempts + 1) ⟨0, base⟩).map
      (fun result => result.bind (fun finished => trialValue finished.1.memory)) =
        (Security.BoundedIntegerSampling.cutoff size attempts).law.map
          (Option.map fun value => BitVec.ofNat 256 value.val) := by
  have law := boundedSampler_run size attempts base positive bounded countFits
  have projected := congrArg
    (PMF.map (fun result : Option (Option Word × Nat) => result.bind Prod.fst)) law
  simp only [PMF.map_comp, Function.comp_def, Option.bind_some] at projected
  rw [← retryLaw_source size attempts]
  simpa only [Option.bind_map, Function.comp_def] using projected

/-- The sampler reserves at most 1804 instructions per retry and four entry or exit instructions. -/
theorem boundedSampler_cost (size attempts : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    retryFuel size attempts + 1 ≤ 1804 * attempts + 4 ∧
      (boundedSampler size attempts).size + 1 = 25 := by
  have bound := (boundedTrial_cost size positive bounded).1
  constructor
  · unfold retryFuel
    have product := Nat.mul_le_mul_right attempts (show trialCost size + 2 ≤ 1804 by omega)
    omega
  · rfl

/-- The default retry limit reserves at most 461828 instructions and 25 program-table units. -/
theorem boundedSampler_256_cost (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    retryFuel size 256 + 1 + ((boundedSampler size 256).size + 1) ≤ 461853 := by
  obtain ⟨runtime, table⟩ := boundedSampler_cost size 256 positive bounded
  omega

/-- The actual machine has the same geometric failure probability as the source cutoff. -/
theorem boundedSampler_failure [BN254.FieldCertificate] (size attempts : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    ((run (boundedSampler size attempts) (retryFuel size attempts + 1) ⟨0, base⟩).map
      (fun result => result.bind (fun finished => trialValue finished.1.memory))) none =
        Security.BoundedIntegerSampling.rejection size ^ attempts := by
  rw [boundedSampler_source size attempts base positive bounded countFits, PMF.map_apply]
  have accepts : ∀ value : Option (Fin size),
      (none : Option Word) = value.map (fun accepted => BitVec.ofNat 256 accepted.val) ↔ value = none := by
    intro value
    cases value <;> simp
  simp_rw [accepts]
  rw [tsum_ite_eq]
  exact Security.BoundedIntegerSampling.cutoff_none size attempts

/-- The default machine fails with probability at most two to the minus 256. -/
theorem boundedSampler_256_failure [BN254.FieldCertificate] (size : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    ((run (boundedSampler size 256) (retryFuel size 256 + 1) ⟨0, base⟩).map
      (fun result => result.bind (fun finished => trialValue finished.1.memory))) none ≤
        (2 : ENNReal)⁻¹ ^ 256 := by
  rw [boundedSampler_failure size 256 base positive bounded (by decide)]
  exact pow_le_pow_left' (Security.BoundedIntegerSampling.rejection_le_half size positive) 256

end Kriterion.ArgoMAC.ArithmeticSimulator
