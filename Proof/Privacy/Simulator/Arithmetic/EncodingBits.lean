import Proof.Privacy.Simulator.Arithmetic.WireCodec
import Encoding

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The protocol exposes each bit of the specified natural number. -/
theorem protocolBits_get (width value index : Nat) (inside : index < width) :
    (bits width value)[index]'(by simp [bits]; exact inside) = value.testBit index := by
  simp [bits, BitVec.getLsb, BitVec.getLsbD, Nat.testBit_mod_two_pow, inside]

/-- Adjacent little-endian words split at the specified bit position. -/
theorem protocolBits_append (first second value : Nat) :
    bits (first + second) value = bits first value ++ bits second (value / 2 ^ first) := by
  apply List.ext_getElem
  · simp [bits]
  · intro index left right
    have inside : index < first + second := by simpa [bits] using left
    rw [protocolBits_get _ _ _ inside]
    by_cases low : index < first
    · rw [List.getElem_append_left (by simpa [bits] using low), protocolBits_get first value index low]
    · have high : first ≤ index := by omega
      rw [List.getElem_append_right (by simpa [bits] using high)]
      simp only [bits, List.length_map, List.length_finRange] at *
      have offset : index - first < second := by omega
      change value.testBit index = (bits second (value / 2 ^ first))[index - first]'(by simpa [bits] using offset)
      rw [protocolBits_get second _ _ offset, Nat.testBit_div_two_pow, Nat.sub_add_cancel high]

/-- The natural-number encoding emits the same little-endian bits as one word. -/
theorem naturalEncoding_bits (width : Nat) (value : Fin (256 ^ width)) :
    ((Encoding.natural width).encode value).flatMap (fun byte => bits 8 byte.val) =
      bits (8 * width) value.val := by
  induction width with
  | zero => simp [Encoding.natural, bits]
  | succ width ih =>
      simp only [Encoding.natural, Encoding.map, Encoding.pair, Encoding.byte,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [ih]
      have low : bits 8 (value.val % 256) = bits 8 value.val := by
        apply List.ext_getElem
        · simp [bits]
        · intro index left right
          have bound : index < 8 := by simpa [bits] using left
          rw [protocolBits_get _ _ _ bound, protocolBits_get _ _ _ bound]
          simpa only [decide_eq_true bound, Bool.true_and] using Nat.testBit_mod_two_pow value.val 8 index
      rw [low, show 8 * (width + 1) = 8 + 8 * width by omega, protocolBits_append]
      rfl

/-- The vector encoding emits its elements in their array order. -/
theorem vectorEncoding_encode {A : Type} (encoding : Encoding A) (count : Nat) (value : Vector A count) :
    ((encoding.vector count).encode value) = value.toList.flatMap encoding.encode := by
  induction count with
  | zero => rw [show value = #v[] from Vector.eq_empty]; rfl
  | succ count ih =>
      simp only [Encoding.vector, Encoding.map, Encoding.pair]
      rw [ih]
      have rebuilt := congrArg (fun values : Vector A (count + 1) => values.toList.flatMap encoding.encode)
        (Vector.push_pop_back value)
      simpa only [Vector.toList_push, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] using rebuilt

/-- A mapped encoding transmits its forward image. -/
theorem encodingMap_encode {A B : Type} (encoding : Encoding A) (forward : B → A)
    (backward : A → B) (inverse : ∀ value, backward (forward value) = value) (value : B) :
    ((encoding.map forward backward inverse).encode value) = encoding.encode (forward value) := rfl

/-- A paired encoding transmits its first component and then its second. -/
theorem encodingPair_encode {A B : Type} (first : Encoding A) (second : Encoding B)
    (value : A × B) :
    ((first.pair second).encode value) = first.encode value.1 ++ second.encode value.2 := rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
