import Construction.Simulator.StoredInverse
import Proof.Privacy.Simulator.Arithmetic.StoredForward
import Proof.Privacy.Simulator.Arithmetic.SwapMetadata

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The inverse loader implements both fixed instruction lists exactly. -/
theorem inverseLoad_memory (memory : Memory) : executeLinear inverseLoad memory = inverseLoaded memory := by
  unfold inverseLoad executeLinear
  rw [List.foldl_append]
  change executeLinear swapMetadata (executeLinear oracleLoad memory) = _
  rw [oracleLoad_memory, swapMetadata_memory]
  rfl

/-- The inverse commit implements the exchange and count write exactly. -/
theorem inverseCommit_memory (memory : Memory) : executeLinear inverseCommit memory = inverseCommitted memory := by
  unfold inverseCommit executeLinear
  rw [List.foldl_append]
  change executeLinear oracleCommit (executeLinear swapMetadata memory) = _
  rw [swapMetadata_memory, oracleCommit_memory]
  rfl

/-- The inverse loader returns after twenty-nine fixed instructions. -/
theorem inverseLoad_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host inverseLoad labels)
    (memory : Memory) (fuel : Nat) :
    run host (29 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 29, inverseLoaded memory⟩).map
        (Option.map fun result => (result.1, result.2 + 29)) := by
  have length : inverseLoad.length = 29 := rfl
  simpa only [inverseLoad_memory, length] using linear_continue host inverseLoad labels present memory fuel

/-- The inverse commit returns after ten fixed instructions. -/
theorem inverseCommit_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host inverseCommit labels)
    (memory : Memory) (fuel : Nat) :
    run host (10 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 10, inverseCommitted memory⟩).map
        (Option.map fun result => (result.1, result.2 + 10)) := by
  have length : inverseCommit.length = 10 := rfl
  simpa only [inverseCommit_memory, length] using linear_continue host inverseCommit labels present memory fuel

/-- The persistent handler contains every loader instruction. -/
theorem storedInverse_load (attempts : Nat) : ContainsLinear (storedInverse attempts) inverseLoad
    storedInverseLoadLabels := by
  intro index valid
  have bound : index < 29 := valid
  simp [storedInverse, storedInverseLoadLabels, Nat.min_eq_left (by omega : index ≤ 29),
    Nat.min_eq_left (by omega : index + 1 ≤ 29), bound]

/-- The persistent handler contains the complete forward machine. -/
theorem storedInverse_forward (attempts : Nat) :
    ContainsPermutationForward (storedInverse attempts) attempts storedInverseForwardLabels := by
  intro pc valid
  have bound : pc.val < 153 := by
    have small := pc.isLt
    have different : pc.val ≠ 153 := by intro eq; apply valid; exact Fin.ext eq
    omega
  simp [storedInverse, storedInverseForwardLabels, show ¬ pc.val + 29 < 29 by omega,
    show pc.val + 29 < 182 by omega]
  rfl

/-- The persistent handler contains every commit instruction. -/
theorem storedInverse_commit (attempts : Nat) : ContainsLinear (storedInverse attempts) inverseCommit
    storedInverseCommitLabels := by
  intro index valid
  have bound : index < 10 := valid
  simp [storedInverse, storedInverseCommitLabels, Nat.min_eq_left (by omega : index ≤ 10),
    Nat.min_eq_left (by omega : index + 1 ≤ 10), show ¬ 182 + index < 29 by omega,
    show ¬ 182 + index < 182 by omega, show 182 ≤ 182 + index by omega,
    show 182 + index < 192 by omega, Nat.add_assoc]

/-- The source persists the returned count after the forward-query source on exchanged tables. -/
noncomputable def storedInverseSamples (attempts count : Nat) (memory : Memory) : PMF (Memory × Nat) :=
  (permutationForwardSamples attempts count count (inverseLoaded memory)).map fun result =>
    (inverseCommitted result.1, result.2 + 39)

/-- The commit and final halt consume exactly eleven instructions. -/
theorem storedInverse_finish [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (storedInverse attempts) (11 + extra) ⟨182, memory⟩ =
      PMF.pure (some (⟨192, inverseCommitted memory⟩, 11)) := by
  rw [show 11 + extra = 10 + (extra + 1) by omega]
  have committed := inverseCommit_continue (storedInverse attempts) storedInverseCommitLabels
    (storedInverse_commit attempts) memory (extra + 1)
  change run (storedInverse attempts) (10 + (extra + 1)) ⟨182, memory⟩ = _ at committed
  rw [committed]
  have halted : (storedInverse attempts).code[(192 : Fin ((storedInverse attempts).size + 1)).val] =
      .halt := by simp [storedInverse]
  change (run (storedInverse attempts) (extra + 1) ⟨192, inverseCommitted memory⟩).map _ = _
  simp only [run, step, halted, PMF.pure_bind, PMF.pure_map, Option.map_some]

/-- The persistent handler implements loading, the full query, and the charged commit. -/
theorem storedInverse_run [BN254.FieldCertificate] (attempts count : Nat) (memory : Memory)
    (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (inverseLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run (storedInverse attempts) (29 + (permutationForwardCost attempts count count (inverseLoaded memory) + 11))
      ⟨0, memory⟩ = (storedInverseSamples attempts count memory).map
        (fun result => some (⟨192, result.1⟩, result.2)) := by
  have inputCounter : (inverseLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have outputCounter : (inverseLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have loaded := inverseLoad_continue (storedInverse attempts) storedInverseLoadLabels (storedInverse_load attempts)
    memory (permutationForwardCost attempts count count (inverseLoaded memory) + 11)
  change run (storedInverse attempts) _ ⟨0, memory⟩ = _ at loaded
  rw [loaded]
  have forward := permutationForwardBlock_continue (storedInverse attempts) attempts count count 11
    storedInverseForwardLabels (storedInverse_forward attempts) (inverseLoaded memory) countFits tableFits tableFits
    inputCounter outputCounter
  dsimp only at forward
  change run (storedInverse attempts) _ ⟨29, inverseLoaded memory⟩ = _ at forward
  change (run (storedInverse attempts) _ ⟨29, inverseLoaded memory⟩).map _ = _
  rw [forward, PMF.map_bind]
  unfold storedInverseSamples
  simp only [PMF.map_comp, Function.comp_def]
  change (permutationForwardSamples attempts count count (inverseLoaded memory)).bind _ =
    (permutationForwardSamples attempts count count (inverseLoaded memory)).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have costBound := permutationForwardSamples_cost attempts count count (inverseLoaded memory) final cost
    countFits tableFits tableFits inputCounter outputCounter supported
  have costPositive := permutationForwardSamples_positive attempts count count (inverseLoaded memory) final cost supported
  have remaining : 11 ≤ permutationForwardCost attempts count count (inverseLoaded memory) + 11 - (cost - 1) := by omega
  change (run (storedInverse attempts)
    (permutationForwardCost attempts count count (inverseLoaded memory) + 11 - (cost - 1))
    ⟨182, final⟩).map _ = _
  rw [show permutationForwardCost attempts count count (inverseLoaded memory) + 11 - (cost - 1) =
    11 + (permutationForwardCost attempts count count (inverseLoaded memory) + 11 - (cost - 1) - 11) by omega,
    storedInverse_finish, PMF.pure_map]
  have charge : 11 + (cost - 1) + 29 = cost + 39 := by omega
  simp only [Function.comp_def, Option.map_some, charge]

/-- The persistent inverse handler has a concrete linear cost in its stored count. -/
theorem storedInverse_budget (attempts count : Nat) (memory : Memory) :
    (storedInverse attempts).size + 1 + 29 +
      (permutationForwardCost attempts count count (inverseLoaded memory) + 11) ≤
      2574 * attempts + 33 * count + 325 := by
  have bound := permutationForward_budget attempts count count (inverseLoaded memory)
  change 153 + 1 + _ ≤ _ at bound
  change 192 + 1 + 29 + _ ≤ _
  dsimp [permutationForwardCost]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
