import Proof.Privacy.Simulator.Arithmetic.StoredForwardBlock
import Proof.Privacy.Simulator.Arithmetic.StoredInverseBlock
import Proof.Privacy.Simulator.Arithmetic.HashHandlerBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every stored forward result fits the compiled body reserve. -/
theorem storedForwardSamples_cost [BN254.FieldCertificate] (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support) :
    1 ≤ cost ∧ cost ≤ 22 + permutationForwardCost attempts count count (oracleLoaded memory) + 4 := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have inputCounter : (oracleLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have outputCounter : (oracleLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [oracleLoaded] using counter
  have bound := permutationForwardSamples_cost attempts count count (oracleLoaded memory) before spent
    attemptFits tableFits tableFits inputCounter outputCounter member
  have costs := congrArg Prod.snd equal
  dsimp only at costs
  omega

/-- Every stored inverse result fits the compiled body reserve. -/
theorem storedInverseSamples_cost [BN254.FieldCertificate] (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (inverseLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support) :
    1 ≤ cost ∧ cost ≤ 29 + permutationForwardCost attempts count count (inverseLoaded memory) + 11 := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have inputCounter : (inverseLoaded memory).registers 2 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have outputCounter : (inverseLoaded memory).registers 4 = BitVec.ofNat 256 count := by
    simpa [inverseLoaded, metadataSwapped, oracleLoaded] using counter
  have bound := permutationForwardSamples_cost attempts count count (inverseLoaded memory) before spent
    attemptFits tableFits tableFits inputCounter outputCounter member
  have costs := congrArg Prod.snd equal
  dsimp only at costs
  omega

/-- Every sparse hash result fits the scan and exact-word sampling reserve. -/
theorem hashHandlerSamples_cost (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support) :
    1 ≤ cost ∧ cost ≤ (hashScan count memory).2 + 1845 := by
  unfold hashHandlerSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have costs := congrArg Prod.snd equal
  dsimp only at costs
  have tailBound : 1 ≤ spent ∧ spent ≤ 1818 := by
    unfold hashTailSamples at member
    split at member
    · obtain ⟨value, _, equation⟩ := (PMF.mem_support_map_iff _ _ _).mp member
      have tailCost := congrArg Prod.snd equation
      dsimp only at tailCost
      omega
    · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at member
      omega
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
