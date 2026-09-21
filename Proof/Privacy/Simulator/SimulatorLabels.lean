import Proof.Privacy.Simulator.SimulatorProtocol

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
namespace SimulatorMachine

/-- This instruction reads a label pair, reads one input bit, selects one label, and writes that label. -/
def labelWithCost (key : BitAdaptor.Key) (bit : Bool) : Block × Nat :=
  match bit with
  | false => (key.falseLabel, 4)
  | true => (key.trueLabel, 4)

/-- The counted instruction returns the construction's selected label. -/
theorem labelWithCost_value (key : BitAdaptor.Key) (bit : Bool) :
    (labelWithCost key bit).1 = BitAdaptor.encode key bit := by cases bit <;> rfl

/-- The coordinate builder records each executed label-selection instruction. -/
def coordinateLabelsWithCost (key : CoordinateMacKey) (bits : CoordinateBits) : CoordinateMac × Nat :=
  let rows := Vector.ofFn fun index => labelWithCost key[index.val] (bits.getLsb index)
  (rows.map Prod.fst, (rows.map Prod.snd).toList.sum + 2 * coordinateBitCount)

/-- The coordinate builder returns the original label vector. -/
theorem coordinateLabelsWithCost_value (key : CoordinateMacKey) (bits : CoordinateBits) :
    (coordinateLabelsWithCost key bits).1 = encodeCoordinate key bits := by
  apply Vector.ext
  intro index valid
  simp only [coordinateLabelsWithCost, Vector.getElem_map, Vector.getElem_ofFn,
    encodeCoordinate, labelWithCost_value]

/-- The coordinate builder executes six primitive operations for each of 254 labels. -/
theorem coordinateLabelsWithCost_count (key : CoordinateMacKey) (bits : CoordinateBits) :
    (coordinateLabelsWithCost key bits).2 = 1524 := by
  have constant : (Vector.ofFn fun index =>
      labelWithCost key[index.val] (bits.getLsb index)).map Prod.snd =
      Vector.replicate coordinateBitCount 4 := by
    apply Vector.ext
    intro index valid
    simp only [Vector.getElem_map, Vector.getElem_ofFn, Vector.getElem_replicate]
    cases bits.getLsb ⟨index, valid⟩ <;> rfl
  simp only [coordinateLabelsWithCost]
  have total := congrArg (fun values : Vector Nat coordinateBitCount => values.toList.sum) constant
  simp only [Vector.toList_replicate, List.sum_replicate] at total
  rw [total]
  rfl

/-- The label builder converts two coordinates and constructs both selected-label vectors. -/
def labelsWithCost (key : InputMacKey) (input : AffineInput) : Garbling.Labels × Nat :=
  let bits := BitInput.ofAffine input
  let x := coordinateLabelsWithCost key.x bits.xBits
  let y := coordinateLabelsWithCost key.y bits.yBits
  (⟨bits, ⟨x.1, y.1⟩⟩, x.2 + y.2 + 2)

/-- The counted label builder has the original value and an exact fixed-width operation count. -/
theorem labelsWithCost_spec (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) :
    (labelsWithCost coin.2.1 input).1 = (privateView coin).labels input ∧
      (labelsWithCost coin.2.1 input).2 = 3050 := by
  constructor
  · simp only [labelsWithCost, coordinateLabelsWithCost_value]
    rfl
  · simp only [labelsWithCost, coordinateLabelsWithCost_count]

end SimulatorMachine
end Kriterion.ArgoMAC.Security
