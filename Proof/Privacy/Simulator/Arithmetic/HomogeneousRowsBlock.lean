import Proof.Privacy.Simulator.Arithmetic.HomogeneousRowsCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The row body reads one free point in seven instructions. -/
theorem homogeneousRowBlock_load [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1))
    (fuel : Nat) (base : Memory) (one : base.registers 12 = 1) :
    run host (fuel + 7) ⟨labels (homogeneousRowSlot index 0), base⟩ =
      (run host fuel ⟨labels (homogeneousRowSlot index 7), homogeneousRowLoaded base index.val⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  have code := homogeneousRowBlock_load_code host count fits labels present index
  simp [run, step, code 0 (by decide), code 1 (by decide), code 2 (by decide), code 3 (by decide),
    code 4 (by decide), code 5 (by decide), code 6 (by decide), relocate, Arithmetic.eval, one,
    homogeneousRowLoaded, Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The row body reads its canonical scale in three instructions. -/
theorem homogeneousRowBlock_scale [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1))
    (fuel : Nat) (base : Memory) :
    run host (fuel + 3) ⟨labels (homogeneousRowSlot index 7), base⟩ =
      (run host fuel ⟨labels (homogeneousRowSlot index 10), homogeneousRowScaled base index.val⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  have code := homogeneousRowBlock_load_code host count fits labels present index
  simp [run, step, code 7 (by decide), code 8 (by decide), code 9 (by decide), relocate, Arithmetic.eval,
    homogeneousRowScaled, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The row body stores three homogeneous coordinates in seven instructions. -/
theorem homogeneousRowBlock_store [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1))
    (fuel : Nat) (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase)
    (one : base.registers 12 = 1) :
    run host (fuel + 7) ⟨labels (homogeneousRowSlot index 18),
      homogeneousMemory (homogeneousRowScaled base index.val) point scale⟩ =
      (run host fuel ⟨labels (homogeneousRowBoundary (index.val + 1) index.isLt),
        homogeneousRowStored base index.val point scale⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  have code := homogeneousRowBlock_store_code host count fits labels present index
  simp [run, step, code 18 (by decide), code 19 (by decide), code 20 (by decide), code 21 (by decide),
    code 22 (by decide), code 23 (by decide), code 24 (by decide), relocate, Arithmetic.eval,
    homogeneousRowStored, homogeneousMemory, homogeneousRowScaled, homogeneousWords, storeDrawWords,
    one, Function.update_comm, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    BitVec.ofNat_add, BitVec.add_assoc]

/-- The row body converts and stores its accumulator point in fifteen instructions. -/
theorem homogeneousRowBlock_finish [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1))
    (fuel : Nat) (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase)
    (one : base.registers 12 = 1) (encoded : PointAccumulatorEncoding base point)
    (source : base.ram (base.registers 11 + BitVec.ofNat 256 index.val) = BitVec.ofNat 256 scale.value.val) :
    run host (fuel + 15) ⟨labels (homogeneousRowSlot index 7), base⟩ =
      (run host fuel ⟨labels (homogeneousRowBoundary (index.val + 1) index.isLt),
        homogeneousRowStored base index.val point scale⟩).map
        (Option.map fun result => (result.1, result.2 + 15)) := by
  have pointSource : PointAccumulatorEncoding (homogeneousRowScaled base index.val) point := by
    simpa [PointAccumulatorEncoding, homogeneousRowScaled] using encoded
  have scaleSource : (homogeneousRowScaled base index.val).registers 0 = BitVec.ofNat 256 scale.value.val := by
    simpa [homogeneousRowScaled] using source
  have converted := homogeneousPointBlock_run host (labels ∘ homogeneousRowLabels index)
    (homogeneousRowBlock_conversion host count fits labels present index) (fuel + 7)
    (homogeneousRowScaled base index.val) point scale pointSource scaleSource
  rw [show fuel + 15 = (fuel + 7 + 5) + 3 by omega, homogeneousRowBlock_scale host count fits labels present index]
  change (run host (fuel + 7 + 5) ⟨(labels ∘ homogeneousRowLabels index) 0, homogeneousRowScaled base index.val⟩).map _ = _
  rw [converted]
  change ((run host (fuel + 7) ⟨labels (homogeneousRowSlot index 18),
    homogeneousMemory (homogeneousRowScaled base index.val) point scale⟩).map _).map _ = _
  rw [homogeneousRowBlock_store host count fits labels present index fuel base point scale one]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The full row body loads, converts, and stores one free point in 22 instructions. -/
theorem homogeneousRowBlock_run [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 25 * (count + 1) + 1 < 2 ^ 256)
    (labels : Fin (25 * (count + 1) + 2) → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host count fits labels) (index : Fin (count + 1))
    (fuel : Nat) (base : Memory) (point : BN254.Point) (scale : BN254.NonZeroBase)
    (one : base.registers 12 = 1)
    (pointSource : StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (index.val - 1))) point)
    (scaleSource : base.ram (base.registers 11 + BitVec.ofNat 256 index.val) = BitVec.ofNat 256 scale.value.val) :
    run host (fuel + 22) ⟨labels (homogeneousRowBoundary index.val (Nat.le_of_lt index.isLt)), base⟩ =
      (run host fuel ⟨labels (homogeneousRowBoundary (index.val + 1) index.isLt),
        homogeneousRowStored (homogeneousRowLoaded base index.val) index.val point scale⟩).map
        (Option.map fun result => (result.1, result.2 + 22)) := by
  change run host (fuel + 22) ⟨labels (homogeneousRowSlot index 0), base⟩ = _
  rw [show fuel + 22 = (fuel + 15) + 7 by omega, homogeneousRowBlock_load host count fits labels present index _ base one,
    homogeneousRowBlock_finish host count fits labels present index fuel (homogeneousRowLoaded base index.val) point scale
      (by simpa [homogeneousRowLoaded] using one) (homogeneousRowLoaded_encoding base index.val point pointSource)
      (by simpa [homogeneousRowLoaded] using scaleSource)]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
