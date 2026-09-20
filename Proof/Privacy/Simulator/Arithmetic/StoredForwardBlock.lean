import Proof.Privacy.Simulator.Arithmetic.StoredForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the persistent forward handler before its final return. -/
def ContainsStoredForward (host : Machine) (attempts : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 179, pc ≠ 178 → host.code[(labels pc).val] =
    relocate labels ((storedForward attempts).code[pc.val]'(by exact pc.isLt))

/-- The host contains the loader from the persistent handler. -/
theorem storedForwardBlock_load (host : Machine) (attempts : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) (present : ContainsStoredForward host attempts labels) :
    ContainsLinear host oracleLoad (labels ∘ storedLoadLabels) := by
  intro index valid
  have bound : index < 22 := valid
  have inside : storedLoadLabels index ≠ 178 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedLoadLabels, Nat.min_eq_left (by omega : index ≤ 22)] at values
    omega
  exact (present (storedLoadLabels index) inside).trans
    ((congrArg (relocate labels) (storedForward_load attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The host contains the complete sparse forward-query block. -/
theorem storedForwardBlock_forward (host : Machine) (attempts : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) (present : ContainsStoredForward host attempts labels) :
    ContainsPermutationForward host attempts (labels ∘ storedForwardLabels) := by
  intro pc valid
  have inside : storedForwardLabels pc ≠ 178 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedForwardLabels] at values
    omega
  exact (present (storedForwardLabels pc) inside).trans
    ((congrArg (relocate labels) (storedForward_forward attempts pc valid)).trans
      (relocate_comp storedForwardLabels labels _))

/-- The host contains the final count commit. -/
theorem storedForwardBlock_commit (host : Machine) (attempts : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) (present : ContainsStoredForward host attempts labels) :
    ContainsLinear host oracleCommit (labels ∘ storedCommitLabels) := by
  intro index valid
  have bound : index < 3 := valid
  have inside : storedCommitLabels index ≠ 178 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedCommitLabels, Nat.min_eq_left (by omega : index ≤ 3)] at values
    omega
  exact (present (storedCommitLabels index) inside).trans
    ((congrArg (relocate labels) (storedForward_commit attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The body commits its result before it returns to the host. -/
theorem storedForwardBlock_body [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) (present : ContainsStoredForward host attempts labels)
    (initial : Memory) (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (inputCounter : initial.registers 2 = BitVec.ofNat 256 count)
    (outputCounter : initial.registers 4 = BitVec.ofNat 256 count) :
    let reserve := permutationForwardCost attempts count count initial + (3 + fuel)
    run host reserve ⟨labels 22, initial⟩ =
      (permutationForwardSamples attempts count count initial).bind fun result =>
        (run host (reserve - (result.2 + 2)) ⟨labels 178, oracleCommitted result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 + 2))) := by
  dsimp only
  have forward := permutationForwardBlock_continue host attempts count count (3 + fuel)
    (labels ∘ storedForwardLabels) (storedForwardBlock_forward host attempts labels present)
    initial countFits tableFits tableFits inputCounter outputCounter
  dsimp only at forward
  change run host _ ⟨labels 22, initial⟩ = _ at forward
  rw [forward]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have costBound := permutationForwardSamples_cost attempts count count initial final cost
    countFits tableFits tableFits inputCounter outputCounter supported
  have costPositive := permutationForwardSamples_positive attempts count count initial final cost supported
  let remaining := permutationForwardCost attempts count count initial + (3 + fuel) - (cost - 1)
  have available : 3 ≤ remaining := by dsimp [remaining]; omega
  change (run host remaining ⟨labels 175, final⟩).map _ = _
  rw [show remaining = 3 + (remaining - 3) by omega]
  have committed := oracleCommit_continue host (labels ∘ storedCommitLabels)
    (storedForwardBlock_commit host attempts labels present) final (remaining - 3)
  change run host (3 + (remaining - 3)) ⟨labels 175, final⟩ = _ at committed
  rw [committed]
  have charge : cost + 2 = 3 + (cost - 1) := by omega
  have rest : permutationForwardCost attempts count count initial + (3 + fuel) -
      (cost + 2) = remaining - 3 := by dsimp [remaining]; omega
  dsimp only [Function.comp_def]
  rw [rest, charge]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, storedCommitLabels, Nat.add_assoc]

/-- A fixed loader charge distributes over the charged source continuation. -/
theorem storedForwardBlock_charge [BN254.FieldCertificate] (host : Machine) (label : Fin (host.size + 1))
    (reserve : Nat) (source : PMF (Memory × Nat)) :
    (source.bind fun result =>
      (run host (reserve - (result.2 + 2)) ⟨label, oracleCommitted result.1⟩).map
        (Option.map fun final => (final.1, final.2 + (result.2 + 2)))).map
          (Option.map fun final => (final.1, final.2 + 22)) =
    (source.map fun result => (oracleCommitted result.1, result.2 + 25)).bind fun result =>
      (run host (22 + reserve - (result.2 - 1)) ⟨label, result.1⟩).map
        (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext result
  dsimp only [Function.comp_def]
  have rest : 22 + reserve - (result.2 + 25 - 1) = reserve - (result.2 + 2) := by omega
  have charge : result.2 + 25 - 1 = result.2 + 2 + 22 := by omega
  rw [rest, charge]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The persistent handler retains its full source law and unused caller fuel. -/
theorem storedForwardBlock_continue [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 179 → Fin (host.size + 1)) (present : ContainsStoredForward host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    let reserve := 22 + (permutationForwardCost attempts count count (oracleLoaded memory) + (3 + fuel))
    run host reserve ⟨labels 0, memory⟩ =
      (storedForwardSamples attempts count memory).bind fun result =>
        (run host (reserve - (result.2 - 1)) ⟨labels 178, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  dsimp only
  have inputCounter : (oracleLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have outputCounter : (oracleLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have loaded := oracleLoad_continue host (labels ∘ storedLoadLabels)
    (storedForwardBlock_load host attempts labels present) memory
    (permutationForwardCost attempts count count (oracleLoaded memory) + (3 + fuel))
  change run host _ ⟨labels 0, memory⟩ = _ at loaded
  rw [loaded]
  change (run host _ ⟨labels 22, oracleLoaded memory⟩).map _ = _
  rw [storedForwardBlock_body host attempts count fuel labels present (oracleLoaded memory)
    countFits tableFits inputCounter outputCounter]
  exact storedForwardBlock_charge host (labels 178) _ _

end Kriterion.ArgoMAC.ArithmeticSimulator
