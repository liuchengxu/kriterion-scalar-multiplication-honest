import Proof.Privacy.Collision.SharedRetainedFlagsDistribution
import Proof.Privacy.Collision.ConcreteRetainedBadBound
import Proof.Privacy.Distribution.SharedMaskSourceDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype publicVectorFintype
  ciphertextFintype bitAdaptorTableFintype instNonemptyPublicSample_2 circuitMaskSampleFintype
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 instFintypeCircuitMaskTables
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
local instance concreteFlagsRemainder {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable, fun _ _ => defaultHashLiftQuotient)⟩
local instance concreteFlagsRow [FieldCertificate] [GroupCertificate] : Nonempty RetainedRowCoin :=
  ⟨(Classical.arbitrary ClampedAffineOffsets, fun _ => (Seed.randomness 0).curveMask,
    (Seed.randomness 0).curveMask)⟩
local instance concreteFlagsKey : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance concreteFlagsOracle : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩
attribute [local irreducible] PMF.uniformOfFintype sharedRetainedCoinFlags

variable {Aux : Type*}
  (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
  (parameter : Nat) (auxiliary : Aux)

/-- These flags keep the exact shared retained tape and independent public sample. -/
def sharedConcreteRetainedFlags [FieldCertificate] [GroupCertificate] (scalar : ScalarField) : PMF (Bool × Bool) :=
  (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).bind fun source =>
    let split := sharedRetainedSimulatorSourceEquiv source
    sharedRetainedCoinFlags adversary parameter auxiliary (retainedSourceRows scalar source.1.val)
      source.1.val.2.2.1.2.value split.2.1 split.2.2

/-- The shared source split preserves all retained row coefficients. -/
theorem sharedRetainedCoinRows_inverse [FieldCertificate] [GroupCertificate] (scalar : ScalarField)
    (source : SharedPrivateSource) :
    retainedSourceRows scalar (sharedRetainedSimulatorSourceEquiv.symm source).1.val =
      retainedCoinRows scalar source.1 := by
  apply retainedSourceRows_fields

/-- The exact shared flags separate into retained rows and the actual offline coin. -/
theorem sharedConcreteRetainedFlags_split [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    sharedConcreteRetainedFlags adversary parameter auxiliary scalar =
      (PMF.uniformOfFintype RetainedRowCoin).bind fun rowCoin =>
        sharedRetainedFlags adversary parameter auxiliary (retainedCoinRows scalar rowCoin) rowCoin.2.2.value := by
  have law := congrArg (fun distribution => distribution.bind (fun source : SharedPrivateSource =>
    sharedRetainedCoinFlags adversary parameter auxiliary (retainedCoinRows scalar source.1)
      source.1.2.2.value source.2.1 source.2.2)) map_uniform_sharedRetainedSimulatorSource
  rw [PMF.bind_map] at law
  have rows (source : SharedMaskRetainedTape × PublicSample) :
      retainedCoinRows scalar (sharedRetainedSimulatorSourceEquiv source).1 =
        retainedSourceRows scalar source.1.val := by
    have aligned := sharedRetainedCoinRows_inverse scalar (sharedRetainedSimulatorSourceEquiv source)
    rw [Equiv.symm_apply_apply] at aligned
    exact aligned.symm
  simp only [Function.comp_def, rows] at law
  change sharedConcreteRetainedFlags adversary parameter auxiliary scalar = _ at law
  rw [law, uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype RetainedRowCoin).bind
  funext rowCoin
  rw [uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm]
  exact sharedRetainedFlags_offline adversary parameter auxiliary (retainedCoinRows scalar rowCoin) rowCoin.2.2.value

/-- The exact retained source has the joint point-row and shared prequery bound. -/
theorem sharedConcreteRetainedFlags_mass_le [FieldCertificate] [GroupCertificate] (scalar : ScalarField) :
    (sharedConcreteRetainedFlags adversary parameter auxiliary scalar).toOuterMeasure
      {flags | flags.1 = true ∨ flags.2 = true} ≤
        (169786660680 / 1000) / (2 : ENNReal) ^ 128 +
          (364 * adversary.firstQueryBudget parameter : Nat) / (2 : ENNReal) ^ 128 := by
  rw [sharedConcreteRetainedFlags_split]
  apply Probability.bind_event_le
  intro rowCoin _
  exact sharedRetainedFlags_mass_le adversary parameter auxiliary (retainedCoinRows scalar rowCoin) rowCoin.2.2.value

end
end Kriterion.ArgoMAC.Security
