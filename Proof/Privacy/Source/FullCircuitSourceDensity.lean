import Proof.Privacy.Source.RealCircuitSource
import Proof.Privacy.Collision.CircuitSlotRatio

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped BigOperators ENNReal
noncomputable section

attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables
  rawBucketUseFintype instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1

private def tableBlocksEquiv : BitAdaptor.Table ≃ (Fin 2 → Block) :=
  (show BitAdaptor.Table ≃ BitAdaptor.Ciphertext from
    ⟨BitAdaptor.Table.trueRow, fun row => ⟨row⟩, fun _ => rfl, fun _ => rfl⟩).trans ciphertextBlockEquiv

private theorem five_sum (count : Nat) : 3 * count + 2 * count = 5 * count := by omega

/-- The public source has five blocks for each actual circuit gate. -/
theorem fullCircuitSource_card [Fintype Block] :
    Fintype.card FullCircuitSource = Fintype.card Block ^ (5 * Fintype.card RawCircuitGate) := by
  have hashes : Fintype.card FullHashLift = Fintype.card Block ^ 3 :=
    (Fintype.card_congr fullHashLiftBlockEquiv).trans (by rw [Fintype.card_fun, Fintype.card_fin])
  have tables := Fintype.card_congr tableBlocksEquiv
  have family := Fintype.card_congr circuitMaskTablesEquiv
  simp only [Fintype.card_fun, Fintype.card_fin] at tables family
  rw [Fintype.card_prod, Fintype.card_fun, hashes, family, tables]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  exact congrArg (fun exponent => Fintype.card Block ^ exponent)
    (five_sum (Fintype.card RawCircuitGate))

/-- The circuit buckets count all five slots at every gate. -/
theorem circuitBucketSize_sum :
    ∑ index, circuitBucketSize index = 5 * Fintype.card RawCircuitGate := by
  let keys : RawCircuitGate → BitAdaptor.Key := fun _ => ⟨0, 0⟩
  let slopes : RawCircuitGate → BaseField := fun _ => 0
  let lifts : RawCircuitGate → FullHashLift := fun _ => 0
  let tables : RawCircuitGate → BitAdaptor.Table := fun _ => defaultBitAdaptorTable
  let gates := circuitRawGatePrescription keys slopes lifts tables
  have counted := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun use : RawCircuitGate × Pipeline.FixedKeySlot =>
      fixedKeyIndex (gates use.1).location (gates use.1).window use.2))
  change Fintype.card ((index : Pipeline.FixedKeyIndex) × RawBucketUse gates index) = _ at counted
  rw [Fintype.card_sigma, Fintype.card_prod] at counted
  have slots : Fintype.card Pipeline.FixedKeySlot = 5 := by decide
  rw [slots] at counted
  have each : ∀ index, Fintype.card (RawBucketUse gates index) = circuitBucketSize index :=
    fun index => circuitRawBucketUse_card keys slopes lifts tables index
  simp_rw [each] at counted
  exact counted.trans (Nat.mul_comm _ _)

private theorem inverse_power_product {Index : Type*} [Fintype Index]
    (size : Index → Nat) (count : Nat) :
    ((count : ℝ≥0∞) ^ ∑ index, size index)⁻¹ =
      ∏ index, ((count : ℝ≥0∞) ^ size index)⁻¹ := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply ENNReal.prod_inv_distrib
  intro _ _ _ _ _
  exact Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

private theorem uniform_mass_of_card {Source Index : Type*} [Fintype Source] [Nonempty Source]
    [Fintype Index] (size : Index → Nat) (count : Nat)
    (card : Fintype.card Source = count ^ ∑ index, size index) (source : Source) :
    (PMF.uniformOfFintype Source) source = ∏ index, ((count : ℝ≥0∞) ^ size index)⁻¹ := by
  rw [PMF.uniformOfFintype_apply, card, Nat.cast_pow]
  exact inverse_power_product size count

/-- The uniform source has the exact density in the circuit counting ratio. -/
theorem fullCircuitSource_uniform_mass [Fintype Block] (source : FullCircuitSource) :
    (PMF.uniformOfFintype FullCircuitSource) source =
      ∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹ := by
  apply uniform_mass_of_card circuitBucketSize (Fintype.card Block) _ source
  exact fullCircuitSource_card.trans
    (congrArg (fun exponent => Fintype.card Block ^ exponent) circuitBucketSize_sum.symm)

end
end Kriterion.ArgoMAC.Security
