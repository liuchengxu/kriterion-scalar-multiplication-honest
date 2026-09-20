import Construction.Simulator.PointHorner
import Proof.Privacy.Simulator.Arithmetic.PointNegation
import Proof.Privacy.Simulator.Arithmetic.ScalarMulMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The Horner scalar is the paper's fixed radix in canonical word form. -/
def hornerReady (base : Memory) : Memory :=
  {base with registers := Function.update base.registers 0 (BitVec.ofNat 256 radix.val)}

/-- The scalar block returns the exact radix multiple. -/
theorem hornerScaled_spec [BN254.FieldCertificate] [BN254.GroupCertificate] (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some point) :
    readPoint (scalarFinish (hornerReady base) point).registers scalarAccumulator = some (radix • point) ∧
    (scalarFinish (hornerReady base) point).bits = base.bits ∧
    (scalarFinish (hornerReady base) point).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val →
      (scalarFinish (hornerReady base) point).registers register = base.registers register := by
  have ready : readPoint (hornerReady base).registers scalarMultiple = some point := by
    rw [hornerReady, readPoint_update_other base.registers scalarMultiple 0 _ (by decide) (by decide) (by decide)]
    exact input
  have source := scalarFinish_spec (hornerReady base) point ready
  have fits : radix.val < 2 ^ 256 := lt_trans radix.val_lt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
  have scalar : radix.val • point = radix • point := by
    rw [← Nat.cast_smul_eq_nsmul BN254.ScalarField]
    rw [ZMod.natCast_zmod_val]
  constructor
  · simpa only [hornerReady, Function.update_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, scalar] using source.1
  refine ⟨source.2.1, source.2.2.1, ?_⟩
  intro register caller
  have different : register ≠ 0 := by intro equal; have value := congrArg Fin.val equal; omega
  exact (source.2.2.2 register caller).trans (Function.update_of_ne different _ _)

/-- The RAM point uses a tag followed by two canonical coordinate words. -/
def storedPoint [BN254.FieldCertificate] (ram : Word → Word) (address : Word) : Option BN254.Point :=
  readPoint (fun register => if register = 5 then ram address else if register = 6 then ram (address + 1)
    else if register = 7 then ram (address + 1 + 1) else 0) scalarMultiple

/-- The load tail reads one point triple and retains its final address. -/
def hornerLoaded (base : Memory) (index : Nat) : Memory :=
  let address := base.registers 10 + BitVec.ofNat 256 (3 * index)
  {base with registers := Function.update (Function.update (Function.update (Function.update base.registers
    8 (address + 1 + 1)) 5 (base.ram address)) 6 (base.ram (address + 1))) 7 (base.ram (address + 1 + 1))}

/-- The RAM load has the same point value as the stored triple. -/
theorem hornerLoaded_point [BN254.FieldCertificate] (base : Memory) (index : Nat) :
    readPoint (hornerLoaded base index).registers scalarMultiple =
      storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * index)) := by
  simp [hornerLoaded, storedPoint, readPoint, scalarMultiple]

/-- The load tail preserves the scalar accumulator. -/
theorem hornerLoaded_accumulator [BN254.FieldCertificate] (base : Memory) (index : Nat) :
    readPoint (hornerLoaded base index).registers scalarAccumulator = readPoint base.registers scalarAccumulator := by
  apply readPoint_congr <;> simp [hornerLoaded, scalarAccumulator]

/-- The Horner tail adds the next point and copies its canonical sum to the scalar input. -/
def hornerTailMemory [BN254.FieldCertificate] (base : Memory) (index : Nat) (left right : BN254.Point) : Memory :=
  let loaded := hornerLoaded base index
  let added := writePoint loaded.registers scalarAccumulator (left + right)
  {loaded with registers := Function.update (Function.update (Function.update added 5 (added 2)) 6 (added 3)) 7 (added 4)}

/-- The Horner tail returns the exact group sum for the next scalar block. -/
theorem hornerTailMemory_point [BN254.FieldCertificate] (base : Memory) (index : Nat) (left right : BN254.Point) :
    readPoint (hornerTailMemory base index left right).registers scalarMultiple = some (left + right) := by
  have same : readPoint (hornerTailMemory base index left right).registers scalarMultiple =
      readPoint (writePoint (hornerLoaded base index).registers scalarAccumulator (left + right)) scalarAccumulator := by
    simp [readPoint, hornerTailMemory, scalarMultiple, scalarAccumulator]
    rfl
  exact same.trans (scalarAccumulator_write _ _)

/-- The load and add tail preserves every caller register. -/
theorem hornerTailMemory_caller [BN254.FieldCertificate] (base : Memory) (index : Nat) (left right : BN254.Point)
    (register : Register) (caller : 9 ≤ register.val) :
    (hornerTailMemory base index left right).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  simp only [hornerTailMemory, Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 7 (by decide))]
  rw [writePoint_other _ scalarAccumulator _ register (different 2 (by decide)) (different 3 (by decide)) (different 4 (by decide))]
  simp only [hornerLoaded, Function.update_of_ne (different 8 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 7 (by decide))]

end Kriterion.ArgoMAC.ArithmeticSimulator
