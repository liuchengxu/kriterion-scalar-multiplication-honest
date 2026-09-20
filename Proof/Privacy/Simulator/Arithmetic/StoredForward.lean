import Construction.Simulator.StoredForward
import Proof.Privacy.Simulator.Arithmetic.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.PermutationForwardReturn

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The persistent handler contains every loader instruction. -/
theorem storedForward_load (attempts : Nat) : ContainsLinear (storedForward attempts) oracleLoad
    storedLoadLabels := by
  intro index valid
  have bound : index < 22 := valid
  simp [storedForward, storedLoadLabels, Nat.min_eq_left (by omega : index ≤ 22),
    Nat.min_eq_left (by omega : index + 1 ≤ 22), bound]

/-- The persistent handler contains the complete forward machine. -/
theorem storedForward_forward (attempts : Nat) :
    ContainsPermutationForward (storedForward attempts) attempts storedForwardLabels := by
  intro pc valid
  have bound : pc.val < 153 := by
    have small := pc.isLt
    have different : pc.val ≠ 153 := by intro eq; apply valid; exact Fin.ext eq
    omega
  simp [storedForward, storedForwardLabels, show ¬ pc.val + 22 < 22 by omega,
    show pc.val + 22 < 175 by omega]
  rfl

/-- The persistent handler contains every commit instruction. -/
theorem storedForward_commit (attempts : Nat) : ContainsLinear (storedForward attempts) oracleCommit
    storedCommitLabels := by
  intro index valid
  have bound : index < 3 := valid
  simp [storedForward, storedCommitLabels, Nat.min_eq_left (by omega : index ≤ 3),
    Nat.min_eq_left (by omega : index + 1 ≤ 3), show ¬ 175 + index < 22 by omega,
    show ¬ 175 + index < 175 by omega, show 175 ≤ 175 + index by omega,
    show 175 + index < 178 by omega, Nat.add_assoc]

/-- Every source outcome includes at least the final return instruction. -/
theorem permutationForwardSamples_positive (attempts inputCount outputCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts inputCount outputCount memory).support) :
    1 ≤ cost := by
  unfold permutationForwardSamples at supported
  dsimp only at supported
  split at supported
  · obtain ⟨⟨sampled, spent⟩, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have costs := congrArg Prod.snd equal
    dsimp only at costs
    omega
  · simp only [PMF.mem_support_pure_iff] at supported
    have costs := congrArg Prod.snd supported
    dsimp only at costs
    omega

/-- The source persists the returned count after the complete forward-query source. -/
noncomputable def storedForwardSamples (attempts count : Nat) (memory : Memory) : PMF (Memory × Nat) :=
  (permutationForwardSamples attempts count count (oracleLoaded memory)).map fun result =>
    (oracleCommitted result.1, result.2 + 25)

/-- The commit and final halt consume exactly four instructions. -/
theorem storedForward_finish [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (storedForward attempts) (4 + extra) ⟨175, memory⟩ =
      PMF.pure (some (⟨178, oracleCommitted memory⟩, 4)) := by
  rw [show 4 + extra = 3 + (extra + 1) by omega]
  have committed := oracleCommit_continue (storedForward attempts) storedCommitLabels
    (storedForward_commit attempts) memory (extra + 1)
  change run (storedForward attempts) (3 + (extra + 1)) ⟨175, memory⟩ = _ at committed
  rw [committed]
  have halted : (storedForward attempts).code[(178 : Fin ((storedForward attempts).size + 1)).val] =
      .halt := by simp [storedForward]
  change (run (storedForward attempts) (extra + 1) ⟨178, oracleCommitted memory⟩).map _ = _
  simp only [run, step, halted, PMF.pure_bind, PMF.pure_map, Option.map_some]

/-- The persistent handler implements loading, the full query, and the charged commit. -/
theorem storedForward_run [BN254.FieldCertificate] (attempts count : Nat) (memory : Memory)
    (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run (storedForward attempts) (22 + (permutationForwardCost attempts count count (oracleLoaded memory) + 4))
      ⟨0, memory⟩ = (storedForwardSamples attempts count memory).map
        (fun result => some (⟨178, result.1⟩, result.2)) := by
  have inputCounter : (oracleLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have outputCounter : (oracleLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have loaded := oracleLoad_continue (storedForward attempts) storedLoadLabels (storedForward_load attempts)
    memory (permutationForwardCost attempts count count (oracleLoaded memory) + 4)
  change run (storedForward attempts) _ ⟨0, memory⟩ = _ at loaded
  rw [loaded]
  have forward := permutationForwardBlock_continue (storedForward attempts) attempts count count 4
    storedForwardLabels (storedForward_forward attempts) (oracleLoaded memory) countFits tableFits tableFits
    inputCounter outputCounter
  dsimp only at forward
  change run (storedForward attempts) _ ⟨22, oracleLoaded memory⟩ = _ at forward
  change (run (storedForward attempts) _ ⟨22, oracleLoaded memory⟩).map _ = _
  rw [forward, PMF.map_bind]
  unfold storedForwardSamples
  simp only [PMF.map_comp, Function.comp_def]
  change (permutationForwardSamples attempts count count (oracleLoaded memory)).bind _ =
    (permutationForwardSamples attempts count count (oracleLoaded memory)).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have costBound := permutationForwardSamples_cost attempts count count (oracleLoaded memory) final cost
    countFits tableFits tableFits inputCounter outputCounter supported
  have costPositive := permutationForwardSamples_positive attempts count count (oracleLoaded memory) final cost supported
  have remaining : 4 ≤ permutationForwardCost attempts count count (oracleLoaded memory) + 4 - (cost - 1) := by omega
  change (run (storedForward attempts)
    (permutationForwardCost attempts count count (oracleLoaded memory) + 4 - (cost - 1))
    ⟨175, final⟩).map _ = _
  rw [show permutationForwardCost attempts count count (oracleLoaded memory) + 4 - (cost - 1) =
    4 + (permutationForwardCost attempts count count (oracleLoaded memory) + 4 - (cost - 1) - 4) by omega,
    storedForward_finish, PMF.pure_map]
  have charge : 4 + (cost - 1) + 22 = cost + 25 := by omega
  simp only [Function.comp_def, Option.map_some, charge]

/-- The persistent forward handler has a concrete linear cost in its stored count. -/
theorem storedForward_budget (attempts count : Nat) (memory : Memory) :
    (storedForward attempts).size + 1 + 22 +
      (permutationForwardCost attempts count count (oracleLoaded memory) + 4) ≤
      2574 * attempts + 33 * count + 297 := by
  have bound := permutationForward_budget attempts count count (oracleLoaded memory)
  change 153 + 1 + _ ≤ _ at bound
  change 178 + 1 + 22 + _ ≤ _
  dsimp [permutationForwardCost]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
