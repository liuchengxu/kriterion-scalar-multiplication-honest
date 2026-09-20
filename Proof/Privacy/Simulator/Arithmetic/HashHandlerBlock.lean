import Proof.Privacy.Simulator.Arithmetic.FreshChoiceBlock
import Proof.Privacy.Simulator.Arithmetic.HashHandlerBlockCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The loader, setup, and lookup preserve the exact scan prefix. -/
theorem hashHandlerBlock_start [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    runPrefix host ((hashScan count memory).2 + 27) ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 35, (hashScan count memory).1⟩, (hashScan count memory).2 + 27)) := by
  rw [show (hashScan count memory).2 + 27 = 22 + (4 + ((hashScan count memory).2 + 1)) by omega,
    prefix_add]
  have loaded := linear_prefix host oracleLoad (labels ∘ hashLoadLabels) (hashHandlerBlock_load host labels present) memory
  change runPrefix host 22 ⟨labels 0, memory⟩ = _ at loaded
  rw [loaded, PMF.pure_bind]
  change (runPrefix host (4 + ((hashScan count memory).2 + 1))
    ⟨labels 22, executeLinear oracleLoad memory⟩).map _ = _
  rw [oracleLoad_memory, prefix_add]
  have ready := linear_prefix host hashSetup (labels ∘ hashSetupLabels) (hashHandlerBlock_setup host labels present) (oracleLoaded memory)
  change runPrefix host 4 ⟨labels 22, oracleLoaded memory⟩ = _ at ready
  rw [ready, PMF.pure_bind]
  change ((runPrefix host ((hashScan count memory).2 + 1)
    ⟨labels 26, executeLinear hashSetup (oracleLoaded memory)⟩).map _).map _ = _
  rw [hashSetup_memory]
  have scanned := tableBlock_prefix host (labels ∘ hashTableLabels) (hashHandlerBlock_table host labels present) count
    (hashReady (oracleLoaded memory)) fits (by simp [hashReady, counter])
  change runPrefix host ((hashScan count memory).2 + 1) ⟨labels 26, hashReady (oracleLoaded memory)⟩ = _ at scanned
  rw [scanned, PMF.pure_map, PMF.pure_map]
  simp [hashTableLabels, hashScan, show hashSetup.length = 4 from rfl,
    show oracleLoad.length = 22 from rfl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The fresh path samples a full word and returns after 1817 charged instructions. -/
theorem hashHandlerBlock_fresh [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (fuel : Nat) (memory : Memory) (fresh : memory.registers 12 = 0#256) :
    run host (1817 + fuel) ⟨labels 35, memory⟩ =
      (PMF.uniformOfFintype Word).bind fun value =>
        (run host fuel ⟨labels 73, oracleCommitted (hashInstalled (frame memory value 0 0))⟩).map
          (Option.map fun result => (result.1, result.2 + 1817)) := by
  rw [show 1817 + fuel = (1797 + (16 + (3 + fuel))) + 1 by omega,
    hashHandlerBlock_branch host labels present]
  simp only [if_pos fresh]
  have sampled := wordBlock_continue host (16 + (3 + fuel)) (labels ∘ hashWordLabels)
    (hashHandlerBlock_word host labels present) memory
  change run host (1797 + (16 + (3 + fuel))) ⟨labels 39, memory⟩ = _ at sampled
  rw [sampled, PMF.map_bind]
  congr 1
  funext value
  have installed := linear_continue host hashInstall (labels ∘ hashInstallLabels)
    (hashHandlerBlock_install host labels present) (frame memory value 0 0) (3 + fuel)
  change run host (16 + (3 + fuel)) ⟨labels 51, _⟩ = _ at installed
  change ((run host (16 + (3 + fuel)) ⟨labels 51, frame memory value 0 0⟩).map _).map _ = _
  rw [installed, hashInstall_memory]
  have committed := oracleCommit_continue host (labels ∘ hashCommitLabels)
    (hashHandlerBlock_commit host labels present) (hashInstalled (frame memory value 0 0)) fuel
  change run host (3 + fuel) ⟨labels 70, _⟩ = _ at committed
  change (((run host (3 + fuel) ⟨labels 70, hashInstalled (frame memory value 0 0)⟩).map _).map _).map _ = _
  rw [committed]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, show hashInstall.length = 16 from rfl,
    hashCommitLabels, Nat.add_assoc]

/-- The known path returns after seven charged instructions. -/
theorem hashHandlerBlock_found [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (fuel : Nat) (memory : Memory) (found : memory.registers 12 ≠ 0#256) :
    run host (7 + fuel) ⟨labels 35, memory⟩ =
      (run host fuel ⟨labels 73, oracleCommitted (hashFound memory)⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  rw [show 7 + fuel = (3 + (3 + fuel)) + 1 by omega, hashHandlerBlock_branch host labels present]
  simp only [if_neg found]
  have known := linear_continue host hashKnown (labels ∘ hashKnownLabels)
    (hashHandlerBlock_known host labels present) memory (3 + fuel)
  change run host (3 + (3 + fuel)) ⟨labels 67, memory⟩ = _ at known
  rw [known, hashKnown_memory]
  have committed := oracleCommit_continue host (labels ∘ hashCommitLabels)
    (hashHandlerBlock_commit host labels present) (hashFound memory) fuel
  change run host (3 + fuel) ⟨labels 70, _⟩ = _ at committed
  change ((run host (3 + fuel) ⟨labels 70, hashFound memory⟩).map _).map _ = _
  rw [committed]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, show hashKnown.length = 3 from rfl,
    hashCommitLabels, Nat.add_assoc]

/-- The two hash paths retain their exact cost and unused caller fuel. -/
theorem hashHandlerBlock_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (fuel : Nat) (memory : Memory) :
    run host (1817 + fuel) ⟨labels 35, memory⟩ =
      (hashTailSamples memory).bind fun result =>
        (run host (1817 + fuel - (result.2 - 1)) ⟨labels 73, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  by_cases fresh : memory.registers 12 = 0#256
  · rw [hashHandlerBlock_fresh host labels present fuel memory fresh]
    simp only [hashTailSamples, if_pos fresh, PMF.bind_map, Function.comp_def]
    change _ = (coinFold 256 0).bind _
    rw [coinFold_word_uniform]
    simp
  · rw [show 1817 + fuel = 7 + (1810 + fuel) by omega,
      hashHandlerBlock_found host labels present (1810 + fuel) memory fresh]
    simp [hashTailSamples, fresh, PMF.pure_bind, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

/-- The full host contract retains the complete sparse hash source and its exact charge. -/
theorem hashHandlerBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (count fuel : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    let reserve := (hashScan count memory).2 + 1844 + fuel
    run host reserve ⟨labels 0, memory⟩ =
      (hashHandlerSamples count memory).bind fun result =>
        (run host (reserve - (result.2 - 1)) ⟨labels 73, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  dsimp only
  rw [show (hashScan count memory).2 + 1844 + fuel =
      ((hashScan count memory).2 + 27) + (1817 + fuel) by omega,
    run_after_prefix, hashHandlerBlock_start host labels present count memory fits counter, PMF.pure_bind]
  dsimp only
  rw [hashHandlerBlock_tail host labels present, PMF.map_bind]
  unfold hashHandlerSamples
  rw [PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have positive : 1 ≤ cost := by
    unfold hashTailSamples at supported
    split at supported
    · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have costs := congrArg Prod.snd equal
      dsimp only at costs
      omega
    · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      omega
  have charge : cost + (hashScan count memory).2 + 27 - 1 =
      (cost - 1) + ((hashScan count memory).2 + 27) := by omega
  have remaining : (hashScan count memory).2 + 27 + (1817 + fuel) -
      ((cost - 1) + ((hashScan count memory).2 + 27)) = 1817 + fuel - (cost - 1) := by omega
  dsimp only [Function.comp_def]
  rw [charge, remaining]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
