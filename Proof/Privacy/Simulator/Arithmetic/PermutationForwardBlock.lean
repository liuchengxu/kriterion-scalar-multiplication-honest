import Proof.Privacy.Simulator.Arithmetic.PermutationForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the full forward handler before its return instruction. -/
def ContainsPermutationForward (host : Machine) (attempts : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 154, pc ≠ 153 → host.code[(labels pc).val] =
    relocate labels ((permutationForward attempts).code[pc.val]'(by exact pc.isLt))

/-- The host contains the known-query block. -/
theorem permutationForwardBlock_known (host : Machine) (attempts : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) (present : ContainsPermutationForward host attempts labels) :
    ContainsKnownQuery host (labels ∘ permutationKnownLabels) := by
  intro pc valid
  have inside : permutationKnownLabels pc ≠ 153 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [permutationKnownLabels] at values
    omega
  exact (present (permutationKnownLabels pc) inside).trans
    ((congrArg (relocate labels) (permutationForward_known attempts pc valid)).trans
      (relocate_comp permutationKnownLabels labels _))

/-- The host contains the fresh-query block. -/
theorem permutationForwardBlock_fresh (host : Machine) (attempts : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) (present : ContainsPermutationForward host attempts labels) :
    ContainsFreshQuery host attempts (labels ∘ permutationFreshLabels) := by
  intro pc valid
  have inside : permutationFreshLabels pc ≠ 153 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [permutationFreshLabels] at values
    have different : pc.val ≠ 114 := by intro eq; apply valid; exact Fin.ext eq
    omega
  exact (present (permutationFreshLabels pc) inside).trans
    ((congrArg (relocate labels) (permutationForward_fresh attempts pc valid)).trans
      (relocate_comp permutationFreshLabels labels _))

/-- The host selects the fresh path or its return in one instruction. -/
theorem permutationForwardBlock_branch [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) (present : ContainsPermutationForward host attempts labels)
    (memory : Memory) :
    run host (fuel + 1) ⟨labels 38, memory⟩ =
      (run host fuel ⟨if memory.registers 7 = 0#256 then labels 39 else labels 153, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  simp [run, step, present 38 (by decide), permutationForward, relocate]

/-- The forward handler retains every sampled state and all unused caller fuel. -/
theorem permutationForwardBlock_run [BN254.FieldCertificate] (host : Machine)
    (attempts inputCount outputCount fuel : Nat)
    (labels : Fin 154 → Fin (host.size + 1)) (present : ContainsPermutationForward host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256)
    (inputFits : inputCount < 2 ^ 256) (outputFits : outputCount < 2 ^ 256)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 inputCount)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 outputCount) :
    let known := knownQueryScan inputCount outputCount memory
    let reserve := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
      3 + (20 + (11 * outputCount + 37 + fuel))
    run host (known.2 + 15 + reserve) ⟨labels 0, memory⟩ =
      if known.1.registers 7 = 0#256 then
        (freshChoiceSamples attempts known.1).bind fun result =>
          let tail := freshQueryTail outputCount (freshChoiceFinal result.1)
          (run host (reserve - (result.2 + 1) - (freshChoiceTailCost result.1 - 1) - (tail.2 - 1))
            ⟨labels 153, tail.1⟩).map
            (Option.map fun final => (final.1, final.2 + (tail.2 - 1) +
              (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15 + known.2))
      else (run host (15 + reserve) ⟨labels 153, known.1⟩).map
        (Option.map fun final => (final.1, final.2 + known.2)) := by
  dsimp only
  let known := knownQueryScan inputCount outputCount memory
  let reserve := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
    3 + (20 + (11 * outputCount + 37 + fuel))
  have positive : 1 ≤ known.2 := by dsimp [known, knownQueryScan]; omega
  rw [show (knownQueryScan inputCount outputCount memory).2 + 15 +
    ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts +
      3 + (20 + (11 * outputCount + 37 + fuel))) =
        (known.2 - 1) + ((15 + reserve) + 1) by change known.2 + 15 + reserve = _; omega]
  have continued := knownQueryBlock_continue host (labels ∘ permutationKnownLabels)
    (permutationForwardBlock_known host attempts labels present) inputCount outputCount memory
    inputFits outputFits inputCounter outputCounter ((15 + reserve) + 1)
  change run host _ ⟨labels 0, memory⟩ = _ at continued
  rw [continued]
  change (run host ((15 + reserve) + 1) ⟨labels 38, known.1⟩).map _ = _
  rw [permutationForwardBlock_branch host attempts (15 + reserve) labels present known.1]
  change _ = if known.1.registers 7 = 0#256 then _ else _
  by_cases fresh : known.1.registers 7 = 0#256
  · simp only [if_pos fresh]
    have full := freshQueryBlock_run host attempts outputCount fuel (labels ∘ permutationFreshLabels)
      (permutationForwardBlock_fresh host attempts labels present) known.1 countFits outputFits
      (by rw [knownQueryScan_metadata _ _ _ 4 (by decide)]; exact outputCounter)
    have boundEq : known.1.registers 5 - known.1.registers 0 =
        memory.registers 5 - memory.registers 0 := by
      rw [knownQueryScan_metadata _ _ _ 5 (by decide), knownQueryScan_metadata _ _ _ 0 (by decide)]
    dsimp only at full
    rw [boundEq] at full
    change run host (15 + reserve) ⟨labels 39, known.1⟩ = _ at full
    rw [full, PMF.map_bind, PMF.map_bind]
    change (freshChoiceSamples attempts known.1).bind _ =
      (freshChoiceSamples attempts known.1).bind _
    congr 1
    funext result
    simp only [PMF.map_comp, Option.map_map, Function.comp_def]
    congr 1
    funext final
    cases final with
    | none => rfl
    | some final =>
        simp only [Option.map_some]
        congr 2
        change _ + 1 + (known.2 - 1) = _ + known.2
        omega
  · simp only [if_neg fresh, PMF.map_comp, Option.map_map, Function.comp_def]
    congr 1
    funext final
    cases final with
    | none => rfl
    | some final =>
        simp only [Option.map_some]
        congr 2
        change final.2 + 1 + (known.2 - 1) = final.2 + known.2
        omega

end Kriterion.ArgoMAC.ArithmeticSimulator
