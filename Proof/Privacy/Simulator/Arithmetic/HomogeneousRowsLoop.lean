import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsSources

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The first prefix starts after its unused free-point load. -/
def homogeneousPrefixLabel {count : Nat} (n : Nat) (inside : n ≤ count + 1) : Fin (25 * (count + 1) + 2) :=
  if n = 0 then ⟨8, by omega⟩ else homogeneousRowBoundary n inside

/-- The first row omits seven free-point load instructions. -/
def homogeneousPrefixCost (n : Nat) : Nat := if n = 0 then 0 else 22 * n - 7

/-- Every row prefix returns the exact target memory with its complete instruction charge. -/
theorem homogeneousRowsBlock_prefix [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels)
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (n : Nat) (inside : n ≤ count + 1)
    (fuel : Nat) (base : Memory) (one : base.registers 12 = 1)
    (encoded : PointAccumulatorEncoding base (points 0))
    (pointSource : ∀ i, i < count + 1 → i ≠ 0 →
      StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1))) (points i))
    (scaleSource : ∀ i, i < count + 1 →
      base.ram (base.registers 11 + BitVec.ofNat 256 i) = BitVec.ofNat 256 (scales i).value.val)
    (separate : HomogeneousRegionsDisjoint base (count + 1)) :
    run host (fuel + homogeneousPrefixCost n) ⟨labels (homogeneousPrefixLabel 0 (by omega)), base⟩ =
      (run host fuel ⟨labels (homogeneousPrefixLabel n inside), homogeneousRowsPrefixMemory points scales n base⟩).map
        (Option.map fun result => (result.1, result.2 + homogeneousPrefixCost n)) := by
  induction n generalizing fuel with
  | zero =>
      simp only [homogeneousPrefixCost, ite_true, Nat.add_zero, homogeneousRowsPrefixMemory]
      have identity : (Option.map fun result : Configuration (host.size + 1) × Nat => (result.1, result.2)) = id := by
        funext result; cases result <;> rfl
      rw [identity, PMF.map_id]
  | succ n ih =>
      by_cases zero : n = 0
      · subst n
        have first := homogeneousRowBlock_finish host count fits labels present ⟨0, by omega⟩ fuel base
          (points 0) (scales 0) one encoded (scaleSource 0 (by omega))
        simpa [homogeneousPrefixCost, homogeneousPrefixLabel, homogeneousRowsPrefixMemory,
          homogeneousRowInput, homogeneousRowSlot] using first
      · have before : n ≤ count + 1 := by omega
        have source := homogeneousRowsPrefixMemory_point points scales n (count + 1) base before separate n (by omega)
          zero (pointSource n (by omega) zero)
        have scale := homogeneousRowsPrefixMemory_scale points scales n (count + 1) base before separate n (by omega)
          (scaleSource n (by omega))
        have next := homogeneousRowBlock_run host count fits labels present ⟨n, by omega⟩ fuel
          (homogeneousRowsPrefixMemory points scales n base) (points n) (scales n)
          ((homogeneousRowsPrefixMemory_caller points scales n base 12 (by decide)).trans one) source scale
        have cost : homogeneousPrefixCost (n + 1) = homogeneousPrefixCost n + 22 := by
          simp only [homogeneousPrefixCost, if_neg zero, if_neg (by omega : n + 1 ≠ 0)]
          omega
        rw [cost, show fuel + (homogeneousPrefixCost n + 22) = (fuel + 22) + homogeneousPrefixCost n by omega,
          ih before (fuel + 22)]
        rw [show homogeneousPrefixLabel n before = homogeneousRowBoundary n before by simp [homogeneousPrefixLabel, zero], next]
        simp only [PMF.map_comp, Option.map_map, Function.comp_def]
        have memory : homogeneousRowsPrefixMemory points scales (n + 1) base =
            homogeneousRowStored (homogeneousRowLoaded (homogeneousRowsPrefixMemory points scales n base) n)
              n (points n) (scales n) := by simp only [homogeneousRowsPrefixMemory, homogeneousRowInput, if_neg zero]
        rw [memory]
        simp only [homogeneousPrefixLabel, if_neg (by omega : n + 1 ≠ 0)]
        apply congrArg (fun transform => PMF.map transform _)
        funext result
        cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The row machine fixes the increment register before its first row. -/
def homogeneousRowsInitial (base : Memory) : Memory :=
  {base with registers := Function.update base.registers 12 1}

/-- The host initializes its increment register in one charged instruction. -/
theorem homogeneousRowsBlock_initialize [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (fuel : Nat) (base : Memory) :
    run host (fuel + 1) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels (homogeneousPrefixLabel 0 (by omega)), homogeneousRowsInitial base⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  have code := present ⟨0, by omega⟩ (by change 0 < 25 * (count + 1) + 1; omega)
  simp only [homogeneousRows, Vector.getElem_ofFn] at code
  simp at code
  change run host (fuel + 1) ⟨labels ⟨0, by omega⟩, base⟩ = _
  simp [run, step, code, relocate, homogeneousPrefixLabel, homogeneousRowsInitial]

/-- The complete target-row memory includes the fixed increment register. -/
def homogeneousRowsMemory [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) (base : Memory) : Memory :=
  homogeneousRowsPrefixMemory points scales (count + 1) (homogeneousRowsInitial base)

/-- The host computes every target row with its exact instruction charge. -/
theorem homogeneousRowsBlock_run [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels)
    (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase) (fuel : Nat) (base : Memory)
    (encoded : PointAccumulatorEncoding base (points 0))
    (pointSource : ∀ i, i < count + 1 → i ≠ 0 →
      StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1))) (points i))
    (scaleSource : ∀ i, i < count + 1 →
      base.ram (base.registers 11 + BitVec.ofNat 256 i) = BitVec.ofNat 256 (scales i).value.val)
    (separate : HomogeneousRegionsDisjoint base (count + 1)) :
    run host (fuel + (22 * count + 16)) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels (homogeneousRowBoundary (count + 1) (Nat.le_refl _)),
        homogeneousRowsMemory points scales count base⟩).map
        (Option.map fun result => (result.1, result.2 + (22 * count + 16))) := by
  have after := homogeneousRowsBlock_prefix host count fits labels present points scales (count + 1) (Nat.le_refl _) fuel
    (homogeneousRowsInitial base) (by simp [homogeneousRowsInitial])
    (by simpa [PointAccumulatorEncoding, homogeneousRowsInitial] using encoded)
    (by simpa [homogeneousRowsInitial] using pointSource)
    (by simpa [homogeneousRowsInitial] using scaleSource)
    (by simpa [HomogeneousRegionsDisjoint, homogeneousRowsInitial] using separate)
  have cost : homogeneousPrefixCost (count + 1) + 1 = 22 * count + 16 := by
    simp only [homogeneousPrefixCost, if_neg (by omega : count + 1 ≠ 0)]
    omega
  rw [← cost, show fuel + (homogeneousPrefixCost (count + 1) + 1) = (fuel + homogeneousPrefixCost (count + 1)) + 1 by omega,
    homogeneousRowsBlock_initialize host count fits labels present, after]
  simp only [homogeneousPrefixLabel, if_neg (by omega : count + 1 ≠ 0), PMF.map_comp, Option.map_map, Function.comp_def]
  change (run host fuel ⟨labels (homogeneousRowBoundary (count + 1) (Nat.le_refl _)),
    homogeneousRowsMemory points scales count base⟩).map _ = _
  apply congrArg (fun transform => PMF.map transform _)
  funext result
  cases result <;> simp [Nat.add_assoc]

/-- The complete target computation stores its exact homogeneous source words. -/
theorem homogeneousRowsMemory_ram [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) (base : Memory) :
    (homogeneousRowsMemory points scales count base).ram =
      storeDrawWords (base.registers 13) 0 base.ram (homogeneousRowsWords points scales (count + 1)) := by
  rw [homogeneousRowsMemory, homogeneousRowsPrefixMemory_ram]
  rfl

/-- The complete target computation preserves every bit stack. -/
theorem homogeneousRowsMemory_bits [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) (base : Memory) : (homogeneousRowsMemory points scales count base).bits = base.bits := by
  rw [homogeneousRowsMemory, homogeneousRowsPrefixMemory_bits]
  rfl

/-- The complete target computation preserves every caller register except its increment register. -/
theorem homogeneousRowsMemory_caller [BN254.FieldCertificate] (points : Nat → BN254.Point) (scales : Nat → BN254.NonZeroBase)
    (count : Nat) (base : Memory) (register : Register) (caller : 9 ≤ register.val) (outside : register ≠ 12) :
    (homogeneousRowsMemory points scales count base).registers register = base.registers register := by
  rw [homogeneousRowsMemory, homogeneousRowsPrefixMemory_caller _ _ _ _ register caller]
  exact Function.update_of_ne outside _ _

end Kriterion.ArgoMAC.ArithmeticSimulator
