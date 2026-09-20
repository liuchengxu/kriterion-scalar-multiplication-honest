import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsMemory
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

attribute [local irreducible] selectedLabelsFor selectedLabelsProgram

/-- The finite index list preserves the vector's original order. -/
theorem vector_toList_finRange {A : Type} {count : Nat} (values : Vector A count) :
    values.toList = (List.finRange count).map values.get := by
  apply List.ext_getElem
  · simp
  · intro index first second
    simp [Vector.get]

/-- The complete emitter produces exactly the original 508 selected labels. -/
theorem selectedLabelsProgram_bits [BN254.FieldCertificate] (coin : OfflineCoin) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    (executeLinear selectedLabelsProgram base).bits = Function.update base.bits 3
      ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).toList.flatMap
        (fun value => GarbledCircuit.SimulatorProtocol.bits 128 value.toNat) ++ base.bits 3) := by
  rw [selectedLabelsProgram_eq, selectedLabelsFor_bits, vector_toList_finRange, List.flatMap_map]
  apply congrArg (Function.update base.bits 3)
  apply congrArg (fun words => words ++ base.bits 3)
  apply congrArg (fun encode => (List.finRange 508).flatMap encode)
  funext index
  rw [selectedLabelWord_source coin input base stored coordinates index, BitVec.toNat_setWidth_of_le (by decide)]

end Kriterion.ArgoMAC.ArithmeticSimulator
