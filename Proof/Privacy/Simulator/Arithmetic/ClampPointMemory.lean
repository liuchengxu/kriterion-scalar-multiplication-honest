import Construction.Simulator.ClampPoint
import Proof.Privacy.Simulator.Arithmetic.PointHornerLoop

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The canonical point write removes unused identity coordinates. -/
def clampCanonical [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) : Memory :=
  {base with registers := writePoint (Function.update base.registers 5 0) scalarAccumulator point}

/-- The canonical point write supplies every accumulator word. -/
theorem clampCanonical_encoding [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) :
    PointAccumulatorEncoding (clampCanonical base point) point := by
  cases point <;> simp [PointAccumulatorEncoding, clampCanonical, writePoint, scalarAccumulator]

/-- The canonical accumulator words decode to their source point. -/
theorem accumulatorEncoding_read [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (encoded : PointAccumulatorEncoding base point) :
    readPoint base.registers scalarAccumulator = some point := by
  apply Eq.trans _ (scalarAccumulator_write (fun _ => 0) point)
  exact readPoint_congr base.registers _ scalarAccumulator encoded.1 encoded.2.1 encoded.2.2

/-- The selected output reader converts protocol tags into machine point tags. -/
def selectedOutputPoint [BN254.FieldCertificate] (ram : Word → Word) (pointer : Word) : Option BN254.Point :=
  readPoint (fun register => if register = 5 then ram (pointer + 2) &&& 1
    else if register = 6 then ram (pointer + 3) else if register = 7 then ram (pointer + 4) else 0) scalarMultiple

/-- The final load reads the selected output from its five-word input record. -/
def clampLoaded (base : Memory) : Memory :=
  let pointer := base.registers 11
  {base with registers := Function.update (Function.update (Function.update (Function.update (Function.update
    base.registers 8 (pointer + 4)) 1 1) 5 (base.ram (pointer + 2) &&& 1))
    6 (base.ram (pointer + 3))) 7 (base.ram (pointer + 4))}

/-- The load preserves the correction accumulator. -/
theorem clampLoaded_accumulator [BN254.FieldCertificate] (base : Memory) :
    readPoint (clampLoaded base).registers scalarAccumulator = readPoint base.registers scalarAccumulator := by
  apply readPoint_congr <;> simp [clampLoaded, scalarAccumulator]

/-- The load returns the selected output point. -/
theorem clampLoaded_point [BN254.FieldCertificate] (base : Memory) :
    readPoint (clampLoaded base).registers scalarMultiple = selectedOutputPoint base.ram (base.registers 11) := by
  simp [clampLoaded, selectedOutputPoint, readPoint, scalarMultiple]

/-- The final addition stores the correction in canonical form. -/
def clampAdded [BN254.FieldCertificate] (base : Memory) (negative output : BN254.Point) : Memory :=
  {clampLoaded base with registers := writePoint (clampLoaded base).registers scalarAccumulator (negative + output)}

/-- The correction memory records scalar multiplication, normalization, negation, and addition. -/
def clampPointMemory [BN254.FieldCertificate] [BN254.GroupCertificate] (base : Memory) (current output : BN254.Point) : Memory :=
  clampAdded (pointNegationMemory (clampCanonical (scalarFinish (hornerReady base) current) (radix • current))
    (radix • current)) (-(radix • current)) output

/-- The correction point has the exact source value. -/
theorem clampPointMemory_encoding [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (current output : BN254.Point) :
    PointAccumulatorEncoding (clampPointMemory base current output) (output - radix • current) := by
  have same : -(radix • current) + output = output - radix • current := by rw [sub_eq_add_neg, add_comm]
  simp only [PointAccumulatorEncoding, clampPointMemory, clampAdded, same]
  cases point : output - radix • current <;> simp [writePoint, scalarAccumulator]

end Kriterion.ArgoMAC.ArithmeticSimulator
