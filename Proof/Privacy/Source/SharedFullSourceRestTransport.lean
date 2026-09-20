import Proof.Privacy.Source.SharedFullSourceTape
import Proof.Privacy.Source.FullSourceRestTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance sharedFullSourceRestInputKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This permutation restores the actual rest, full tag, fixed oracle, and input key. -/
def sharedFullSourceRestEquiv [FieldCertificate] [GroupCertificate] :
    (SharedMaskRetainedTape × ((RawCircuitGate → FullHashLift) × CircuitHashRest)) ≃
      GarblingSourceRest × FullCircuitSource × ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :=
  (sharedFullSourceEquiv.symm.trans
    (Equiv.prodCongr sharedGarblingOracleKeyEquiv (Equiv.refl FullCircuitSource))).trans {
      toFun := fun sample => (sample.1.2, sample.2, sample.1.1)
      invFun := fun sample => ((sample.2.2, sample.1), sample.2.1)
      left_inv _ := rfl
      right_inv _ := rfl }

/-- The restored key and rest reconstruct the original complete source tape. -/
theorem sharedFullSourceRest_reconstruct [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    (sharedGarblingOracleKeyEquiv.symm
      ((sharedFullSourceRestEquiv (retained, full)).2.2, (sharedFullSourceRestEquiv (retained, full)).1),
      (sharedFullSourceRestEquiv (retained, full)).2.1) = sharedFullSourceTape retained full := by
  change (sharedGarblingOracleKeyEquiv.symm (sharedGarblingOracleKeyEquiv (sharedFullSourceTape retained full).1),
    (sharedFullSourceTape retained full).2) = _
  rw [Equiv.symm_apply_apply]

/-- Every source weight has the exact actual-rest, tag, oracle, and key average. -/
theorem sharedFullSourceRest_weighted_eq [FieldCertificate] [GroupCertificate]
    [Fintype SharedMaskRetainedTape]
    [Fintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)]
    (witness : Shared.Randomness)
    (weight : Shared.Randomness → FullCircuitSource → ℝ≥0∞) :
    letI : Nonempty SharedMaskRetainedTape := ⟨sharedMaskRetainedTape witness⟩
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (∑' retained : SharedMaskRetainedTape, (PMF.uniformOfFintype SharedMaskRetainedTape) retained *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        weight (sharedFullSourceTape retained full).1 (sharedFullSourceTape retained full).2) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample, (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
          weight (sharedGarblingOracleKeyEquiv.symm (sample, rest)) tag := by
  letI : Nonempty SharedMaskRetainedTape := ⟨sharedMaskRetainedTape witness⟩
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  apply fullSourceUniformTransport sharedFullSourceRestEquiv
    (fun retained full => weight (sharedFullSourceTape retained full).1 (sharedFullSourceTape retained full).2)
    (fun rest tag sample => weight (sharedGarblingOracleKeyEquiv.symm (sample, rest)) tag)
  intro retained full
  exact congrArg (fun pair => weight pair.1 pair.2) (sharedFullSourceRest_reconstruct retained full).symm

/-- Every retained observer has the same exact actual-rest source average. -/
theorem sharedFullSourceRest_retained_weighted_eq [FieldCertificate] [GroupCertificate]
    [Fintype SharedMaskRetainedTape]
    [Fintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)]
    [Fintype GarblingSourceRest] [Fintype FullCircuitSource]
    [Fintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)]
    (witness : Shared.Randomness)
    (weight : SharedMaskRetainedTape → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    letI : Nonempty SharedMaskRetainedTape := ⟨sharedMaskRetainedTape witness⟩
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    (∑' retained : SharedMaskRetainedTape, (PMF.uniformOfFintype SharedMaskRetainedTape) retained *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        weight retained full) =
    ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag : FullCircuitSource, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample, (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)) sample *
          weight (sharedMaskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)))
            (tag.1, sharedCircuitHashRest (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val tag.2) := by
  letI : Nonempty SharedMaskRetainedTape := ⟨sharedMaskRetainedTape witness⟩
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  have transported := sharedFullSourceRest_weighted_eq witness
    (fun randomness tag => weight (sharedMaskRetainedTape randomness)
      (tag.1, sharedCircuitHashRest randomness.val tag.2))
  simpa only [sharedFullSourceTape_retained, sharedFullSourceTape_source] using transported

end
end Kriterion.ArgoMAC.Security
