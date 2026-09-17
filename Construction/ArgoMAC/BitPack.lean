/-
This file defines a bit-level packing interface and its single conversion to a
byte `Encoding`.

`Encoding.pair` concatenates byte lists, so every component rounds up to a whole
number of bytes: a 254-bit field element costs 256 bits and a 254 x 254-bit digit
adaptor costs 64,520. A `BitPack` composes the same way at bit granularity and is
converted to an `Encoding` once, at the top of the transmitted value, so the whole
circuit pays one rounding instead of one per component.
-/

import Encoding

namespace Kriterion

/-- A bit packing is a width-bounded bijection onto the naturals below `2 ^ width`. -/
structure BitPack (α : Type) where
  /-- Every value of `α` occupies this many bits. -/
  width : Nat
  /-- This is the packed value. -/
  toNat : α → Nat
  /-- This recovers a value from its packed form. -/
  ofNat : Nat → α
  /-- Packing stays inside the declared width. -/
  toNat_lt : ∀ value, toNat value < 2 ^ width
  /-- Packing loses nothing. -/
  ofNat_toNat : ∀ value, ofNat (toNat value) = value

namespace BitPack

variable {α β : Type}

/-- This transports a packing along a retraction, exactly as `Encoding.map` does. -/
def map (pack : BitPack α) (forward : β → α) (backward : α → β)
    (inverse : ∀ value, backward (forward value) = value) : BitPack β where
  width := pack.width
  toNat value := pack.toNat (forward value)
  ofNat value := backward (pack.ofNat value)
  toNat_lt value := pack.toNat_lt _
  ofNat_toNat value := by rw [pack.ofNat_toNat, inverse]

/-- The first component takes the low bits, so no padding separates the two. -/
def pair (first : BitPack α) (second : BitPack β) : BitPack (α × β) where
  width := first.width + second.width
  toNat value := first.toNat value.1 + 2 ^ first.width * second.toNat value.2
  ofNat value := (first.ofNat (value % 2 ^ first.width), second.ofNat (value / 2 ^ first.width))
  toNat_lt value := by
    have low := first.toNat_lt value.1
    have high : second.toNat value.2 + 1 ≤ 2 ^ second.width := second.toNat_lt value.2
    have step : 2 ^ first.width * (second.toNat value.2 + 1) ≤
        2 ^ first.width * 2 ^ second.width := Nat.mul_le_mul_left _ high
    rw [Nat.mul_add, Nat.mul_one] at step
    rw [Nat.pow_add]
    omega
  ofNat_toNat := by
    rintro ⟨left, right⟩
    have low := first.toNat_lt left
    have positive : 0 < 2 ^ first.width := by positivity
    show (first.ofNat ((first.toNat left + 2 ^ first.width * second.toNat right) %
        2 ^ first.width),
      second.ofNat ((first.toNat left + 2 ^ first.width * second.toNat right) /
        2 ^ first.width)) = (left, right)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low,
      Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt low, Nat.zero_add,
      first.ofNat_toNat, second.ofNat_toNat]

/-- The last entry takes the low bits. -/
def vectorToNat (pack : BitPack α) : (count : Nat) → Vector α count → Nat
  | 0, _ => 0
  | count + 1, values =>
      pack.toNat values.back + 2 ^ pack.width * pack.vectorToNat count values.pop

/-- This inverts `vectorToNat`. -/
def vectorOfNat (pack : BitPack α) : (count : Nat) → Nat → Vector α count
  | 0, _ => #v[]
  | count + 1, value =>
      (pack.vectorOfNat count (value / 2 ^ pack.width)).push
        (pack.ofNat (value % 2 ^ pack.width))

theorem vectorOfNat_vectorToNat (pack : BitPack α) (count : Nat) (values : Vector α count) :
    pack.vectorOfNat count (pack.vectorToNat count values) = values := by
  induction count with
  | zero =>
      apply Vector.ext
      intro index inRange
      exact absurd inRange (by omega)
  | succ count inductionHypothesis =>
      have positive : 0 < 2 ^ pack.width := by positivity
      have bound : pack.toNat values.back < 2 ^ pack.width := pack.toNat_lt _
      have quotient : pack.vectorToNat (count + 1) values / 2 ^ pack.width =
          pack.vectorToNat count values.pop := by
        simp only [vectorToNat]
        rw [Nat.add_mul_div_left _ _ positive, Nat.div_eq_of_lt bound, Nat.zero_add]
      have remainder : pack.vectorToNat (count + 1) values % 2 ^ pack.width =
          pack.toNat values.back := by
        simp only [vectorToNat]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bound]
      show (pack.vectorOfNat count (pack.vectorToNat (count + 1) values / 2 ^ pack.width)).push
        (pack.ofNat (pack.vectorToNat (count + 1) values % 2 ^ pack.width)) = values
      rw [quotient, remainder, inductionHypothesis values.pop, pack.ofNat_toNat]
      exact Vector.push_pop_back values

theorem vectorToNat_lt (pack : BitPack α) (count : Nat) (values : Vector α count) :
    pack.vectorToNat count values < (2 ^ pack.width) ^ count := by
  induction count with
  | zero => simp [vectorToNat]
  | succ count inductionHypothesis =>
      have bound : pack.toNat values.back < 2 ^ pack.width := pack.toNat_lt _
      have tail := inductionHypothesis values.pop
      calc pack.vectorToNat (count + 1) values
          = pack.toNat values.back + 2 ^ pack.width * pack.vectorToNat count values.pop := rfl
        _ < 2 ^ pack.width * (pack.vectorToNat count values.pop + 1) := by
            rw [Nat.mul_add, Nat.mul_one]; omega
        _ ≤ 2 ^ pack.width * (2 ^ pack.width) ^ count := Nat.mul_le_mul_left _ tail
        _ = (2 ^ pack.width) ^ (count + 1) := by ring

/-- A vector packs with no padding between entries. -/
def vector (pack : BitPack α) (count : Nat) : BitPack (Vector α count) where
  width := pack.width * count
  toNat := pack.vectorToNat count
  ofNat := pack.vectorOfNat count
  toNat_lt values := by
    have bound := pack.vectorToNat_lt count values
    rwa [← Nat.pow_mul] at bound
  ofNat_toNat := pack.vectorOfNat_vectorToNat count

@[simp] theorem map_width (pack : BitPack α) (forward : β → α) (backward : α → β)
    (inverse : ∀ value, backward (forward value) = value) :
    (pack.map forward backward inverse).width = pack.width := rfl

@[simp] theorem pair_width (first : BitPack α) (second : BitPack β) :
    (first.pair second).width = first.width + second.width := rfl

@[simp] theorem vector_width (pack : BitPack α) (count : Nat) :
    (pack.vector count).width = pack.width * count := rfl

/-- This is the single rounding to whole bytes. -/
def encoding (pack : BitPack α) (bytes : Nat) (fits : pack.width ≤ 8 * bytes) : Encoding α :=
  (Encoding.natural bytes).map
    (fun value => ⟨pack.toNat value, lt_of_lt_of_le (pack.toNat_lt value) (by
      calc 2 ^ pack.width ≤ 2 ^ (8 * bytes) := Nat.pow_le_pow_right (by norm_num) fits
        _ = 256 ^ bytes := by rw [Nat.pow_mul])⟩)
    (fun value => pack.ofNat value.val)
    (fun value => pack.ofNat_toNat value)

/-- A bit-packed value has one length, whatever the value is. -/
@[simp] theorem encoding_length (pack : BitPack α) (bytes : Nat)
    (fits : pack.width ≤ 8 * bytes) (value : α) :
    ((pack.encoding bytes fits).encode value).length = bytes :=
  Encoding.natural_length bytes _

end BitPack
end Kriterion
