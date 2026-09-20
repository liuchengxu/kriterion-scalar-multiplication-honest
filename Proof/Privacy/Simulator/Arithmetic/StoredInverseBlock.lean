import Proof.Privacy.Simulator.Arithmetic.StoredInverse

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the persistent inverse handler before its final return. -/
def ContainsStoredInverse (host : Machine) (attempts : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 193, pc ≠ 192 → host.code[(labels pc).val] =
    relocate labels ((storedInverse attempts).code[pc.val]'(by exact pc.isLt))

/-- The host contains the loader from the persistent handler. -/
theorem storedInverseBlock_load (host : Machine) (attempts : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) (present : ContainsStoredInverse host attempts labels) :
    ContainsLinear host inverseLoad (labels ∘ storedInverseLoadLabels) := by
  intro index valid
  have bound : index < 29 := valid
  have inside : storedInverseLoadLabels index ≠ 192 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedInverseLoadLabels, Nat.min_eq_left (by omega : index ≤ 29)] at values
    omega
  exact (present (storedInverseLoadLabels index) inside).trans
    ((congrArg (relocate labels) (storedInverse_load attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The host contains the complete sparse forward-query block. -/
theorem storedInverseBlock_forward (host : Machine) (attempts : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) (present : ContainsStoredInverse host attempts labels) :
    ContainsPermutationForward host attempts (labels ∘ storedInverseForwardLabels) := by
  intro pc valid
  have inside : storedInverseForwardLabels pc ≠ 192 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedInverseForwardLabels] at values
    omega
  exact (present (storedInverseForwardLabels pc) inside).trans
    ((congrArg (relocate labels) (storedInverse_forward attempts pc valid)).trans
      (relocate_comp storedInverseForwardLabels labels _))

/-- The host contains the final exchange and count commit. -/
theorem storedInverseBlock_commit (host : Machine) (attempts : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) (present : ContainsStoredInverse host attempts labels) :
    ContainsLinear host inverseCommit (labels ∘ storedInverseCommitLabels) := by
  intro index valid
  have bound : index < 10 := valid
  have inside : storedInverseCommitLabels index ≠ 192 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [storedInverseCommitLabels, Nat.min_eq_left (by omega : index ≤ 10)] at values
    omega
  exact (present (storedInverseCommitLabels index) inside).trans
    ((congrArg (relocate labels) (storedInverse_commit attempts index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

/-- The body commits its result before it returns to the host. -/
theorem storedInverseBlock_body [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) (present : ContainsStoredInverse host attempts labels)
    (initial : Memory) (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (inputCounter : initial.registers 2 = BitVec.ofNat 256 count)
    (outputCounter : initial.registers 4 = BitVec.ofNat 256 count) :
    let reserve := permutationForwardCost attempts count count initial + (10 + fuel)
    run host reserve ⟨labels 29, initial⟩ =
      (permutationForwardSamples attempts count count initial).bind fun result =>
        (run host (reserve - (result.2 + 9)) ⟨labels 192, inverseCommitted result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 + 9))) := by
  dsimp only
  have forward := permutationForwardBlock_continue host attempts count count (10 + fuel)
    (labels ∘ storedInverseForwardLabels) (storedInverseBlock_forward host attempts labels present)
    initial countFits tableFits tableFits inputCounter outputCounter
  dsimp only at forward
  change run host _ ⟨labels 29, initial⟩ = _ at forward
  rw [forward]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have costBound := permutationForwardSamples_cost attempts count count initial final cost
    countFits tableFits tableFits inputCounter outputCounter supported
  have costPositive := permutationForwardSamples_positive attempts count count initial final cost supported
  let remaining := permutationForwardCost attempts count count initial + (10 + fuel) - (cost - 1)
  have available : 10 ≤ remaining := by dsimp [remaining]; omega
  change (run host remaining ⟨labels 182, final⟩).map _ = _
  rw [show remaining = 10 + (remaining - 10) by omega]
  have committed := inverseCommit_continue host (labels ∘ storedInverseCommitLabels)
    (storedInverseBlock_commit host attempts labels present) final (remaining - 10)
  change run host (10 + (remaining - 10)) ⟨labels 182, final⟩ = _ at committed
  rw [committed]
  have charge : cost + 9 = 10 + (cost - 1) := by omega
  have rest : permutationForwardCost attempts count count initial + (10 + fuel) -
      (cost + 9) = remaining - 10 := by dsimp [remaining]; omega
  dsimp only [Function.comp_def]
  rw [rest, charge]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, storedInverseCommitLabels, Nat.add_assoc]

/-- A fixed loader charge distributes over the charged source continuation. -/
theorem storedInverseBlock_charge [BN254.FieldCertificate] (host : Machine) (label : Fin (host.size + 1))
    (reserve : Nat) (source : PMF (Memory × Nat)) :
    (source.bind fun result =>
      (run host (reserve - (result.2 + 9)) ⟨label, inverseCommitted result.1⟩).map
        (Option.map fun final => (final.1, final.2 + (result.2 + 9)))).map
          (Option.map fun final => (final.1, final.2 + 29)) =
    (source.map fun result => (inverseCommitted result.1, result.2 + 39)).bind fun result =>
      (run host (29 + reserve - (result.2 - 1)) ⟨label, result.1⟩).map
        (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext result
  dsimp only [Function.comp_def]
  have rest : 29 + reserve - (result.2 + 39 - 1) = reserve - (result.2 + 9) := by omega
  have charge : result.2 + 39 - 1 = result.2 + 9 + 29 := by omega
  rw [rest, charge]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The persistent handler retains its full source law and unused caller fuel. -/
theorem storedInverseBlock_continue [BN254.FieldCertificate] (host : Machine) (attempts count fuel : Nat)
    (labels : Fin 193 → Fin (host.size + 1)) (present : ContainsStoredInverse host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (inverseLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    let reserve := 29 + (permutationForwardCost attempts count count (inverseLoaded memory) + (10 + fuel))
    run host reserve ⟨labels 0, memory⟩ =
      (storedInverseSamples attempts count memory).bind fun result =>
        (run host (reserve - (result.2 - 1)) ⟨labels 192, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + (result.2 - 1))) := by
  dsimp only
  have inputCounter : (inverseLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have outputCounter : (inverseLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have loaded := inverseLoad_continue host (labels ∘ storedInverseLoadLabels)
    (storedInverseBlock_load host attempts labels present) memory
    (permutationForwardCost attempts count count (inverseLoaded memory) + (10 + fuel))
  change run host _ ⟨labels 0, memory⟩ = _ at loaded
  rw [loaded]
  change (run host _ ⟨labels 29, inverseLoaded memory⟩).map _ = _
  rw [storedInverseBlock_body host attempts count fuel labels present (inverseLoaded memory)
    countFits tableFits inputCounter outputCounter]
  exact storedInverseBlock_charge host (labels 192) _ _

end Kriterion.ArgoMAC.ArithmeticSimulator
