import Proof.Privacy.Simulator.Arithmetic.SamplerMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every sampler instruction before its return label. -/
def ContainsSampler (host : Machine) (size attempts : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 25, pc.val < 24 → host.code[(labels pc).val] =
    relocate labels ((boundedSampler size attempts).code[pc.val]'(by exact pc.isLt))

/-- The embedded sampler retains all trial instructions. -/
theorem samplerBlock_trialCode (host : Machine) (size attempts : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels) :
    ContainsTrial host (min (size.log2 + 1) 256) (BitVec.ofNat 256 size)
      (size == 2 ^ 256) (labels ∘ retryLabels) := by
  intro pc inside
  have selected := present (retryLabels pc) (by change pc.val + 1 < 24; omega)
  have trial := boundedSampler_contains size attempts pc inside
  exact (selected.trans (congrArg (relocate labels) trial)).trans (relocate_comp retryLabels labels _)

/-- The exhausted loop clears its flag and returns after two instructions. -/
theorem samplerBlock_zero [BN254.FieldCertificate] (host : Machine) (size attempts fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (empty : base.registers 4 = 0) :
    run host (fuel + 2) ⟨labels 22, base⟩ =
      (run host fuel ⟨labels 24, {base with registers := Function.update base.registers 7 0}⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  simp [run, step, present 22 (by decide), present 23 (by decide), boundedSampler, relocate,
    empty, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The successful trial returns after one branch instruction. -/
theorem samplerBlock_accept [BN254.FieldCertificate] (host : Machine) (size attempts fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (accepted : base.registers 7 ≠ 0) :
    run host (fuel + 1) ⟨labels 20, base⟩ =
      (run host fuel ⟨labels 24, base⟩).map (Option.map fun result => (result.1, result.2 + 1)) := by
  change base.registers 7 ≠ 0#256 at accepted
  simp [run, step, present 20 (by decide), boundedSampler, relocate, accepted]

/-- The rejected trial decrements its counter before the next guard. -/
theorem samplerBlock_reject [BN254.FieldCertificate] (host : Machine) (size attempts fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (rejected : base.registers 7 = 0) (one : base.registers 1 = 1) :
    run host (fuel + 2) ⟨labels 20, base⟩ =
      (run host fuel
        ⟨labels 22, {base with registers := Function.update base.registers 4 (base.registers 4 - 1)}⟩).map
          (Option.map fun result => (result.1, result.2 + 2)) := by
  simp [run, step, present 20 (by decide), present 21 (by decide), boundedSampler, relocate,
    rejected, one, Arithmetic.eval, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The guard and the trial pass memory and cost to the caller's result branch. -/
theorem samplerBlock_trial [BN254.FieldCertificate] (host : Machine) (size attempts fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (nonzero : base.registers 4 ≠ 0#256) :
    run host (trialCost size + fuel) ⟨labels 22, base⟩ =
      (trialMemory size base).bind fun memory =>
        (run host fuel ⟨labels 20, memory⟩).map
          (Option.map fun result => (result.1, result.2 + trialCost size)) := by
  have costPositive : 1 ≤ trialCost size := by unfold trialCost; split <;> omega
  have guard : step host ⟨labels 22, base⟩ =
      PMF.pure (some (false, ⟨(labels ∘ retryLabels) 0, base⟩)) := by
    simp [step, present 22 (by decide), boundedSampler, relocate, nonzero, retryLabels, Function.comp_def]
  have continued := run_after_prefix host (trialCost size - 1) fuel ⟨(labels ∘ retryLabels) 0, base⟩
  have block := boundedTrial_block host size (labels ∘ retryLabels)
    (samplerBlock_trialCode host size attempts labels present) base positive bounded
  rw [block] at continued
  rw [show trialCost size + fuel = (trialCost size - 1 + fuel) + 1 by omega,
    run, guard, PMF.pure_bind]
  change (run host (trialCost size - 1 + fuel) ⟨(labels ∘ retryLabels) 0, base⟩).map
    (Option.map fun result => (result.1, result.2 + 1)) = _
  rw [continued]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.map_comp]
  apply congrArg (PMF.bind (trialMemory size base))
  funext memory
  change (run host fuel ⟨labels 20, memory⟩).map _ = _
  apply congrArg (fun f => PMF.map f (run host fuel ⟨labels 20, memory⟩))
  funext result
  cases result <;> simp [Nat.add_assoc, Nat.sub_add_cancel costPositive]

/-- The complete loop returns caller memory and retains the unused fuel. -/
theorem samplerBlock_loop [BN254.FieldCertificate] (host : Machine) (size attempts count fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : count < 2 ^ 256)
    (counter : base.registers 4 = BitVec.ofNat 256 count) :
    run host ((trialCost size + 2) * count + 2 + fuel) ⟨labels 22, base⟩ =
      (samplerMemory size count base).bind fun result =>
        (run host ((trialCost size + 2) * count + 2 + fuel - result.2) ⟨labels 24, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  induction count generalizing base with
  | zero =>
      have empty : base.registers 4 = 0 := by simpa using counter
      rw [samplerMemory, PMF.pure_bind]
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.add_comm, Nat.add_sub_cancel] using
        samplerBlock_zero host size attempts fuel labels present base empty
  | succ count ih =>
      have nonzero : base.registers 4 ≠ 0#256 := by
        rw [counter]
        intro equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countFits] at natural
        change count + 1 = 0 at natural
        omega
      have total : (trialCost size + 2) * (count + 1) + 2 + fuel =
          trialCost size + ((trialCost size + 2) * count + 2 + fuel + 2) := by ring
      rw [total, samplerBlock_trial host size attempts _ labels present base positive bounded nonzero,
        samplerMemory, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro memory supported
      obtain ⟨same, one⟩ := trialMemory_registers size base memory supported
      by_cases rejected : memory.registers 7 = 0
      · rw [if_pos rejected, PMF.bind_map,
          samplerBlock_reject host size attempts _ labels present memory rejected one]
        let next : Memory := {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}
        have nextCounter : next.registers 4 = BitVec.ofNat 256 count := by
          simp only [next, Function.update_self]
          rw [same, counter, BitVec.ofNat_add]
          simp
        have previous := ih next (by omega) nextCounter
        change ((run host ((trialCost size + 2) * count + 2 + fuel) ⟨labels 22, next⟩).map _).map _ = _
        rw [previous]
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply congrArg (PMF.bind (samplerMemory size count next))
        funext result
        rcases result with ⟨final, cost⟩
        have remaining : trialCost size + ((trialCost size + 2) * count + 2 + fuel + 2) -
            (cost + trialCost size + 2) = (trialCost size + 2) * count + 2 + fuel - cost := by omega
        rw [remaining]
        apply congrArg (fun f => PMF.map f
          (run host ((trialCost size + 2) * count + 2 + fuel - cost) ⟨labels 24, final⟩))
        funext result
        cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · rw [if_neg rejected, PMF.pure_bind]
        rw [show (trialCost size + 2) * count + 2 + fuel + 2 =
          ((trialCost size + 2) * count + 2 + fuel + 1) + 1 by omega,
          samplerBlock_accept host size attempts _ labels present memory rejected]
        have remaining : trialCost size + (((trialCost size + 2) * count + 2 + fuel + 1) + 1) -
            (trialCost size + 1) = (trialCost size + 2) * count + 2 + fuel + 1 := by omega
        rw [remaining]
        simp only [PMF.map_comp, Function.comp_def, Option.map_map]
        apply congrArg (fun f => PMF.map f (run host ((trialCost size + 2) * count + 2 + fuel + 1)
          ⟨labels 24, memory⟩))
        funext result
        cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The caller resumes after the complete sampler and retains every unused fuel unit. -/
theorem samplerBlock_run [BN254.FieldCertificate] (host : Machine) (size attempts fuel : Nat)
    (labels : Fin 25 → Fin (host.size + 1)) (present : ContainsSampler host size attempts labels)
    (base : Memory) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    run host ((trialCost size + 2) * attempts + 3 + fuel) ⟨labels 0, base⟩ =
      (samplerMemory size attempts
        {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}).bind fun result =>
          (run host ((trialCost size + 2) * attempts + 3 + fuel - (result.2 + 1))
            ⟨labels 24, result.1⟩).map (Option.map fun final => (final.1, final.2 + result.2 + 1)) := by
  let initialized : Memory := {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}
  have entry : step host ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 22, initialized⟩)) := by
    simp [step, present 0 (by decide), boundedSampler, relocate, initialized]
  have loop := samplerBlock_loop host size attempts attempts fuel labels present initialized
    positive bounded countFits (by simp [initialized])
  rw [show (trialCost size + 2) * attempts + 3 + fuel =
    ((trialCost size + 2) * attempts + 2 + fuel) + 1 by omega, run, entry, PMF.pure_bind]
  change (run host ((trialCost size + 2) * attempts + 2 + fuel) ⟨labels 22, initialized⟩).map _ = _
  rw [loop, PMF.map_bind]
  apply congrArg (PMF.bind (samplerMemory size attempts initialized))
  funext result
  rcases result with ⟨memory, cost⟩
  have remaining : ((trialCost size + 2) * attempts + 2 + fuel) + 1 - (cost + 1) =
      (trialCost size + 2) * attempts + 2 + fuel - cost := by omega
  rw [remaining]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
