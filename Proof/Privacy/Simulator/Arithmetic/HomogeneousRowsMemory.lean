import Construction.Simulator.HomogeneousRows
import Proof.Privacy.Simulator.Arithmetic.ClampPoint
import Proof.Privacy.Simulator.Arithmetic.PointHornerSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source point encoding fixes the three canonical RAM words. -/
def StoredPointEncoding [BN254.FieldCertificate] (ram : Word → Word) (address : Word) (point : BN254.Point) : Prop :=
  ram address = (writePoint (fun _ => 0) scalarAccumulator point) 2 ∧
  ram (address + 1) = (writePoint (fun _ => 0) scalarAccumulator point) 3 ∧
  ram (address + 1 + 1) = (writePoint (fun _ => 0) scalarAccumulator point) 4

/-- The row load reads one free point into the accumulator. -/
def homogeneousRowLoaded (base : Memory) (index : Nat) : Memory :=
  let address := base.registers 10 + BitVec.ofNat 256 (3 * (index - 1))
  {base with registers := Function.update (Function.update (Function.update (Function.update base.registers
    8 (address + 1 + 1)) 2 (base.ram address)) 3 (base.ram (address + 1))) 4 (base.ram (address + 1 + 1))}

/-- The point load preserves the exact canonical source encoding. -/
theorem homogeneousRowLoaded_encoding [BN254.FieldCertificate] (base : Memory) (index : Nat) (point : BN254.Point)
    (source : StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (index - 1))) point) :
    PointAccumulatorEncoding (homogeneousRowLoaded base index) point := by
  simpa [StoredPointEncoding, PointAccumulatorEncoding, homogeneousRowLoaded] using source

/-- The scale load reads one canonical nonzero field word. -/
def homogeneousRowScaled (base : Memory) (index : Nat) : Memory :=
  let address := base.registers 11 + BitVec.ofNat 256 index
  {base with registers := Function.update (Function.update base.registers 8 address) 0 (base.ram address)}

/-- Each homogeneous row stores three canonical field words. -/
def homogeneousWords (value : FieldMacToECMac.HomogeneousValue) : List Word :=
  [BitVec.ofNat 256 value.x.val, BitVec.ofNat 256 value.y.val, BitVec.ofNat 256 value.z.val]

/-- The row store writes the exact homogeneous source words. -/
def homogeneousRowStored [BN254.FieldCertificate] (base : Memory) (index : Nat)
    (point : BN254.Point) (scale : BN254.NonZeroBase) : Memory :=
  let converted := homogeneousMemory (homogeneousRowScaled base index) point scale
  {converted with
    registers := Function.update converted.registers 8 (base.registers 13 + BitVec.ofNat 256 (3 * index + 2)),
    ram := storeDrawWords (base.registers 13) (3 * index) base.ram (homogeneousWords (Security.homogeneousOfPoint point scale))}

/-- The row transformation preserves every caller register. -/
theorem homogeneousRowStored_caller [BN254.FieldCertificate] (base : Memory) (index : Nat)
    (point : BN254.Point) (scale : BN254.NonZeroBase) (register : Register) (caller : 9 ≤ register.val) :
    (homogeneousRowStored base index point scale).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  simp only [homogeneousRowStored, Function.update_of_ne (different 8 (by decide))]
  rw [homogeneousMemory_register _ _ _ register (Or.inr caller)]
  simp only [homogeneousRowScaled, Function.update_of_ne (different 0 (by decide)),
    Function.update_of_ne (different 8 (by decide))]

end Kriterion.ArgoMAC.ArithmeticSimulator
