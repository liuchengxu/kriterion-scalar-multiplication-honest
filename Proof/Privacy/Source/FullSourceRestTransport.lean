import Proof.Privacy.Source.FullSourceTape
import Proof.Privacy.Source.RealSourceSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This permutation restores the actual rest, full tag, fixed oracle, and input key. -/
def fullSourceRestEquiv [FieldCertificate] [GroupCertificate] :
    (MaskRetainedTape × ((RawCircuitGate → FullHashLift) × CircuitHashRest)) ≃
      GarblingSourceRest × FullCircuitSource × ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :=
  ((sharedHashSourceEquiv (RawCircuitGate → FullHashLift)).symm.trans
    (Equiv.prodCongr garblingOracleKeyEquiv (Equiv.refl FullCircuitSource))).trans {
      toFun := fun sample => (sample.1.2, sample.2, sample.1.1)
      invFun := fun sample => ((sample.2.2, sample.1), sample.2.1)
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The restored key and rest reconstruct the original complete source tape. -/
theorem fullSourceRest_reconstruct [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    (garblingOracleKeyEquiv.symm
      ((fullSourceRestEquiv (retained, full)).2.2, (fullSourceRestEquiv (retained, full)).1),
      (fullSourceRestEquiv (retained, full)).2.1) = fullSourceTape retained full := by
  change (garblingOracleKeyEquiv.symm (garblingOracleKeyEquiv (fullSourceTape retained full).1),
    (fullSourceTape retained full).2) = _
  rw [Equiv.symm_apply_apply]

private theorem uniformPair {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

theorem fullSourceUniformTransport {A B C D E : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype E]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty E]
    (equivalence : (A × B) ≃ C × D × E)
    (oldWeight : A → B → ℝ≥0∞) (newWeight : C → D → E → ℝ≥0∞)
    (same : ∀ a b, oldWeight a b = newWeight (equivalence (a, b)).1
      (equivalence (a, b)).2.1 (equivalence (a, b)).2.2) :
    (∑' a, (PMF.uniformOfFintype A) a * ∑' b, (PMF.uniformOfFintype B) b * oldWeight a b) =
    ∑' c, (PMF.uniformOfFintype C) c * ∑' d, (PMF.uniformOfFintype D) d *
      ∑' e, (PMF.uniformOfFintype E) e * newWeight c d e := by
  rw [← uniformPair (fun pair : A × B => oldWeight pair.1 pair.2)]
  have reindex := equivalence.tsum_eq
    (fun sample => (PMF.uniformOfFintype (C × D × E)) sample * newWeight sample.1 sample.2.1 sample.2.2)
  have point (pair : A × B) :
      (PMF.uniformOfFintype (A × B)) pair * oldWeight pair.1 pair.2 =
      (PMF.uniformOfFintype (C × D × E)) (equivalence pair) *
        newWeight (equivalence pair).1 (equivalence pair).2.1 (equivalence pair).2.2 := by
    rw [same]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalence]
  rw [tsum_congr point, reindex]
  rw [uniformPair (fun sample : C × D × E => newWeight sample.1 sample.2.1 sample.2.2)]
  apply tsum_congr
  intro c
  apply congrArg (_ * ·)
  exact uniformPair _

/-- Every source weight has the exact actual-rest, tag, oracle, and key average. -/
theorem fullSourceRest_weighted_eq [FieldCertificate] [GroupCertificate]
    [Fintype MaskRetainedTape]
    [Fintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)]
    (witness : Garbling.Randomness)
    (weight : Garbling.Randomness → FullCircuitSource → ℝ≥0∞) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    (∑' retained : MaskRetainedTape, (PMF.uniformOfFintype MaskRetainedTape) retained *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        weight (fullSourceTape retained full).1 (fullSourceTape retained full).2) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample, (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) sample *
          weight (garblingOracleKeyEquiv.symm (sample, rest)) tag := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  apply fullSourceUniformTransport fullSourceRestEquiv
    (fun retained full => weight (fullSourceTape retained full).1 (fullSourceTape retained full).2)
    (fun rest tag sample => weight (garblingOracleKeyEquiv.symm (sample, rest)) tag)
  intro retained full
  exact congrArg (fun pair => weight pair.1 pair.2) (fullSourceRest_reconstruct retained full).symm

/-- Every retained observer has the same exact actual-rest source average. -/
theorem fullSourceRest_retained_weighted_eq [FieldCertificate] [GroupCertificate]
    [Fintype MaskRetainedTape]
    [Fintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)]
    (witness : Garbling.Randomness)
    (weight : MaskRetainedTape → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    (∑' retained : MaskRetainedTape, (PMF.uniformOfFintype MaskRetainedTape) retained *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        weight retained full) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample, (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) sample *
          weight (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest)))
            (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  have transported := fullSourceRest_weighted_eq witness
    (fun randomness tag => weight (maskRetainedTape randomness)
      (tag.1, sharedCircuitHashRest randomness tag.2))
  simpa only [fullSourceTape_retained, fullSourceTape_source] using transported

end
end Kriterion.ArgoMAC.Security
