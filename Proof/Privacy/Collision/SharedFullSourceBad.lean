import Proof.Privacy.Collision.SharedMaskSourceBad
import Proof.Privacy.Distribution.SharedHashRounding

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance fullBadRemainder {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable, fun _ _ => defaultHashLiftQuotient)⟩
attribute [local irreducible] PMF.uniformOfFintype circuitMaskSampleGarble

variable {Aux : Type*}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- The full source flag rejects incomplete hash fibers before it checks the prefix guard. -/
def sharedFullRetainedBadObserver [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape) (source : (RawCircuitGate → FullHashLift) × CircuitHashRest) : PMF Bool :=
  if FullSourceComplete source.1 then
    sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained (decodeFullSource source)
  else PMF.pure true

/-- Every sampled good hash fiber gives the exact mask-source guard. -/
theorem sharedFullRetainedBadObserver_good [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (retained : SharedMaskRetainedTape)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest) :
    sharedFullRetainedBadObserver adversary parameter auxiliary scalar retained
      ((fun gate => goodHashLiftSource (source.1 gate)), source.2) =
    sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained (circuitMaskHashSplitEquiv.symm source) := by
  have complete : FullSourceComplete (fun gate => goodHashLiftSource (source.1 gate)) :=
    fun gate => ⟨source.1 gate, rfl⟩
  rw [sharedFullRetainedBadObserver, if_pos complete]
  simp only [decodeFullSource, fullSourceHashPair_good]

/-- The full source keeps the exact shared retained tape distribution. -/
def sharedFullRetainedBadSource [FieldCertificate] [GroupCertificate] (scalar : ScalarField) : PMF Bool :=
  (PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind
      (sharedFullRetainedBadObserver adversary parameter auxiliary scalar retained)

/-- The complete source pays only the joint collision loss and one hash-rounding loss. -/
theorem sharedFullRetainedBadSource_mass_le [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    ((sharedFullRetainedBadSource adversary parameter auxiliary scalar).toOuterMeasure {flag | flag = true}).toReal ≤
      (169786660680 / 1000) / (2 : ℝ) ^ 128 +
        (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ℝ) ^ 128 +
        (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have rounding := sharedRetainedHashRounding_observation_bound
    (PMF.uniformOfFintype SharedMaskRetainedTape)
    (sharedFullRetainedBadObserver adversary parameter auxiliary scalar) {flag | flag = true}
  simp_rw [sharedFullRetainedBadObserver_good] at rounding
  have goodLaw :
      ((PMF.uniformOfFintype SharedMaskRetainedTape).bind fun retained =>
        (PMF.uniformOfFintype ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitHashRest)).bind
          (fun source => sharedMaskSourceBadObserver adversary parameter auxiliary scalar retained
            (circuitMaskHashSplitEquiv.symm source))) =
      sharedGoodMaskSourceBad adversary parameter auxiliary scalar := by
    unfold sharedGoodMaskSourceBad
    apply congrArg (PMF.uniformOfFintype SharedMaskRetainedTape).bind
    funext retained
    rw [← map_uniform_circuitMaskHashSplit, PMF.bind_map]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
  rw [goodLaw] at rounding
  have good := ENNReal.toReal_mono (by finiteness)
    (sharedGoodMaskSourceBad_mass_le adversary parameter auxiliary scalar)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at good
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at good
  have upper := (abs_le.mp rounding).2
  change ((sharedFullRetainedBadSource adversary parameter auxiliary scalar).toOuterMeasure _).toReal - _ ≤ _ at upper
  linarith

end
end Kriterion.ArgoMAC.Security
