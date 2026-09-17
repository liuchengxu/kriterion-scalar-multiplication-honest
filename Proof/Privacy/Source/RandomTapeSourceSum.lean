import Proof.Privacy.Source.HiddenHashSource
import Proof.Privacy.Source.FullSourceRestTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] instFintypeInputMacKey_proof_3
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
  instDecidableEqRawCircuitGate_1
attribute [local instance] instNonemptyInputMacKey_proof_3

/-- The weighted bind sum keeps each source probability exactly once. -/
theorem pmf_bind_weighted_sum {Source Target : Type*} (samples : PMF Source)
    (kernel : Source → PMF Target) (weight : Target → ℝ≥0∞) :
    (∑' target, (samples.bind kernel) target * weight target) =
      ∑' source, samples source * ∑' target, kernel source target * weight target := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

set_option maxRecDepth 4096 in
/-- The full tag weight splits into the actual rest, tag, and fixed-oracle/key sum. -/
theorem randomTape_fullTag_weighted [blockFinite : Fintype Block]
    [tagFinite : Fintype FullCircuitSource]
    (witness : Garbling.Randomness) (parameter : Nat)
    (weight : Garbling.Randomness → FullCircuitSource → ℝ≥0∞) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    (∑' randomness, (randomTape witness parameter) randomness *
      ∑' tag, (PMF.uniformOfFintype FullCircuitSource) tag * weight randomness tag) =
    ∑' rest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' tag, (PMF.uniformOfFintype FullCircuitSource) tag *
        ∑' sample, (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)) sample *
          weight (garblingOracleKeyEquiv.symm (sample, rest)) tag := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  rw [@randomTape_oracleKey blockFinite Pipeline.instFintypeFixedKeyIndex witness parameter,
    pmf_bind_weighted_sum]
  apply tsum_congr
  intro rest
  apply congrArg ((PMF.uniformOfFintype GarblingSourceRest) rest * ·)
  rw [pmf_map_weighted_sum]
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro tag
  apply tsum_congr
  intro sample
  ac_rfl

end
end Kriterion.ArgoMAC.Security
