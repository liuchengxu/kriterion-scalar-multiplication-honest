import Construction.Simulator.PublicWire
import Proof.Privacy.Simulator.Arithmetic.PublicWireEncoding

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 100000

/-! ## Emitter blocks

Each transmitted block emits one payload per field or one payload per ciphertext
row. The blocks below state, against the RAM the offline source wrote, exactly
which bits each block contributes, so a row proof only has to supply the word
lookups. -/

/-- The X row's digit tables in their RAM order: y6, y8, y10, then x9. -/
def xDigitAt (table : Biquadratic.PackedXTable) (gate : Nat) :
    Vector BitAdaptor.PackedTable coordinateBitCount :=
  match gate with
  | 0 => table.y6
  | 1 => table.y8
  | 2 => table.y10
  | _ => table.x9

/-- The Y row's digit tables in their RAM order: y6, x7, then x9. -/
def yDigitAt (table : Biquadratic.PackedYTable) (gate : Nat) :
    Vector BitAdaptor.PackedTable coordinateBitCount :=
  match gate with
  | 0 => table.y6
  | 1 => table.x7
  | _ => table.x9

/-- The Z row's digit tables in their RAM order: y6, y8, y10, x7, then x9. -/
def zDigitAt (table : Biquadratic.PackedZTable) (gate : Nat) :
    Vector BitAdaptor.PackedTable coordinateBitCount :=
  match gate with
  | 0 => table.y6
  | 1 => table.y8
  | 2 => table.y10
  | 3 => table.x7
  | _ => table.x9

/-- The curve gadget's digit tables in their RAM order: x3, x5, x7, y4, y6. -/
def curveDigitAt (table : CurveMembership.PackedTable) (gate : Nat) :
    Vector BitAdaptor.PackedTable coordinateBitCount :=
  match gate with
  | 0 => table.x3
  | 1 => table.x5
  | 2 => table.x7
  | 3 => table.y4
  | _ => table.y6

/-- The curve gadget's three coefficients in their RAM order. -/
def curveCoefficients (table : CurveMembership.PackedTable) :
    List BaseField := [table.c0, table.c1, table.c2]

/-- One payload segment emits the low bits of its stored word. -/
theorem wireStored_bits (offset : Nat) (ram : Word → Word) (pointer : Word) :
    (wireStored offset).wire ram pointer =
      bits coordinateBitCount (ram (pointer + BitVec.ofNat 256 offset)).toNat := rfl

/-- One pad segment emits its zero bits. -/
theorem wirePad_bits (width : Fin 8) (ram : Word → Word) (pointer : Word) :
    (wirePad width).wire ram pointer = bits width.val 0 := rfl

/-- A coefficient group with no following pad emits one payload per coefficient. -/
theorem wireCoefficients_flatMap (base : Nat) (values : List BaseField)
    (ram : Word → Word) (pointer : Word)
    (stored : ∀ index : Fin values.length,
      ram (pointer + BitVec.ofNat 256 (base + index.val)) =
        BitVec.ofNat 256 (values.get index).val) :
    (wireCoefficients base values.length).flatMap (WireSegment.wire ram pointer) =
      values.flatMap (fun value => bits coordinateBitCount value.val) := by
  rw [wireCoefficients, List.flatMap_map]
  have expand : (fun index : Fin values.length =>
      (wireStored (base + index.val)).wire ram pointer) =
      (fun index : Fin values.length =>
        bits coordinateBitCount (values.get index).val) := by
    funext index
    rw [wireStored_bits, stored index, fieldBits_value]
  rw [expand, ← List.flatMap_map values.get
    (fun value => bits coordinateBitCount value.val), List.map_get_finRange]

/-- A coefficient group emits its coefficients in order and then its pad. -/
theorem wireCoefficients_bits (base : Nat) (pad : Fin 8) (values : List BaseField)
    (ram : Word → Word) (pointer : Word)
    (stored : ∀ index : Fin values.length,
      ram (pointer + BitVec.ofNat 256 (base + index.val)) =
        BitVec.ofNat 256 (values.get index).val) :
    (wireCoefficients base values.length ++ [wirePad pad]).flatMap
        (WireSegment.wire ram pointer) =
      values.flatMap (fun value => bits coordinateBitCount value.val) ++ bits pad.val 0 := by
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    wireCoefficients_flatMap base values ram pointer stored, wirePad_bits]

/-- The RAM holds the transmitted rows of one digit adaptor at their transmitted
addresses. Only the `coordinateBitCount` transmitted bits are pinned: the two top
bits of a ciphertext are pad, `Table.garble` XORs an arbitrary Davies--Meyer pad
into them, and the emitted wire reads only the transmitted bits. -/
def PayloadStored (ram : Word → Word) (pointer : Word) (base : Nat)
    (value : Vector BitAdaptor.PackedTable coordinateBitCount) : Prop :=
  ∀ index : Fin coordinateBitCount,
    (ram (pointer + BitVec.ofNat 256 (base + index.val))).toNat % 2 ^ coordinateBitCount =
      (value.get index).trueRow.toNat

/-- A stored ciphertext row satisfies the payload hypothesis of its digit table. -/
theorem payloadStored_row (ram : Word → Word) (pointer : Word) (base : Nat)
    (rows : Vector BitAdaptor.Table coordinateBitCount) (index : Fin coordinateBitCount)
    (word : ram (pointer + BitVec.ofNat 256 (base + index.val)) = (rows.get index).trueRow) :
    (ram (pointer + BitVec.ofNat 256 (base + index.val))).toNat % 2 ^ coordinateBitCount =
      ((DigitAdaptor.pack rows).get index).trueRow.toNat := by
  rw [word, DigitAdaptor.pack, Vector.get_map, BitAdaptor.Table.pack, BitAdaptor.payload]
  exact (BitVec.toNat_setWidth coordinateBitCount (rows.get index).trueRow).symm

/-- A digit table emits its rows from the last index down and then its pad. -/
theorem wireDigit_bits (base : Nat) (value : Vector BitAdaptor.PackedTable coordinateBitCount)
    (ram : Word → Word) (pointer : Word)
    (stored : PayloadStored ram pointer base value) :
    (wireDigit base).flatMap (WireSegment.wire ram pointer) =
      value.toList.reverse.flatMap (fun row => bits coordinateBitCount row.trueRow.toNat) ++
        bits 4 0 := by
  rw [wireDigit, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    wirePad_bits]
  congr 1
  rw [List.flatMap_map]
  have expand : (fun index : Fin coordinateBitCount =>
      (wireStored (base + index.val)).wire ram pointer) =
      (fun index : Fin coordinateBitCount => bits coordinateBitCount (value.get index).trueRow.toNat) := by
    funext index
    rw [wireStored_bits, ← protocolBits_mod coordinateBitCount
        (ram (pointer + BitVec.ofNat 256 (base + index.val))).toNat,
      stored index]
  rw [expand, ← List.flatMap_map value.get
      (fun row => bits coordinateBitCount row.trueRow.toNat), List.map_reverse,
    ← vectorToList_finRange value]

/-- A digit group emits the named tables in transmitted order. -/
theorem wireDigits_bits (base : Nat) (gates : List Nat)
    (rows : Nat → Vector BitAdaptor.PackedTable coordinateBitCount)
    (ram : Word → Word) (pointer : Word)
    (stored : ∀ gate ∈ gates, PayloadStored ram pointer (base + coordinateBitCount * gate)
      (rows gate)) :
    (wireDigits base gates).flatMap (WireSegment.wire ram pointer) =
      gates.flatMap (fun gate => (rows gate).toList.reverse.flatMap
        (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) := by
  induction gates with
  | nil => simp [wireDigits]
  | cons head tail ih =>
      have headStored : PayloadStored ram pointer (base + coordinateBitCount * head) (rows head) :=
        fun index => stored head (by simp) index
      have tailStored : ∀ gate ∈ tail, PayloadStored ram pointer
          (base + coordinateBitCount * gate) (rows gate) :=
        fun gate member index => stored gate (by simp [member]) index
      have headResult := wireDigit_bits (base + coordinateBitCount * head) (rows head) ram pointer
        headStored
      have tailResult : tail.flatMap (fun gate => (wireDigit (base + coordinateBitCount * gate)).flatMap
          (WireSegment.wire ram pointer)) =
          tail.flatMap (fun gate => (rows gate).toList.reverse.flatMap
            (fun row => bits coordinateBitCount row.trueRow.toNat) ++ bits 4 0) := by
        rw [← List.flatMap_assoc]
        exact ih tailStored
      rw [wireDigits, List.flatMap_cons, List.flatMap_append, List.flatMap_assoc, headResult,
        tailResult, List.flatMap_cons]

/-- A three-entry gate list emits its blocks in order. -/
theorem flatMap_three {α β : Type} (step : α → List β) (a b c : α) :
    ([a, b, c] : List α).flatMap step = step a ++ (step b ++ (step c ++ [])) := rfl

/-- A four-entry gate list emits its blocks in order. -/
theorem flatMap_four {α β : Type} (step : α → List β) (a b c d : α) :
    ([a, b, c, d] : List α).flatMap step =
      step a ++ (step b ++ (step c ++ (step d ++ []))) := rfl

/-- A five-entry gate list emits its blocks in order. -/
theorem flatMap_five {α β : Type} (step : α → List β) (a b c d e : α) :
    ([a, b, c, d, e] : List α).flatMap step =
      step a ++ (step b ++ (step c ++ (step d ++ (step e ++ [])))) := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
