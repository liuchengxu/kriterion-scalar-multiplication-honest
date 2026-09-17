/-
This file defines one bit adaptor.
-/

import BN254
import Cryptography.Primitives

namespace Kriterion.ArgoMAC

abbrev coordinateBitCount : Nat := 254

namespace BitAdaptor

open BN254 Cryptography

/-- A byte MAC key stores the labels for zero and one. -/
structure Key where
  falseLabel : Block
  trueLabel : Block
deriving DecidableEq

def encode (key : Key) (value : Bool) : Block :=
  if value then key.trueLabel else key.falseLabel

/-- One field MAC uses two AES blocks. -/
abbrev Ciphertext := BitVec 256

/-- A published row keeps only the bits a field element can occupy. The two
top bits of a ciphertext are pad, never message, so they are not transmitted. -/
abbrev Payload := BitVec coordinateBitCount

/-- This projection is the transmitted part of one ciphertext. -/
def payload (ciphertext : Ciphertext) : Payload :=
  ciphertext.setWidth coordinateBitCount

/-- The pRPM boundary supplies the Davies--Meyer hash and encryption maps.
Decryption reads the transmitted payload, not the full ciphertext. -/
structure FixedKeyOracle where
  hashToField : Block → BaseField
  encrypt : Block → BaseField → Ciphertext
  decrypt : Block → Payload → BaseField
  decryptEncrypt : ∀ label message,
    decrypt label (payload (encrypt label message)) = message

/-- Each bucket uses three hash permutations and two pad permutations. -/
structure FixedKeyPermutations where
  hash : Fin 3 → Equiv Block Block
  pad : Fin 2 → Equiv Block Block

def hashBytes (permutations : FixedKeyPermutations) (label : Block) : BitVec 384 :=
  daviesMeyer (permutations.hash 2) label ++
    daviesMeyer (permutations.hash 1) label ++
      daviesMeyer (permutations.hash 0) label

def padBytes (permutations : FixedKeyPermutations) (label : Block) : Ciphertext :=
  daviesMeyer (permutations.pad 1) label ++
    daviesMeyer (permutations.pad 0) label

def fieldBytes (value : BaseField) : Ciphertext :=
  BitVec.ofNat 256 value.val

/-- This oracle uses Davies--Meyer and a little-endian block layout.
The evaluator recomputes the pad, so it needs only the payload bits. -/
def fixedKeyOracle (permutations : FixedKeyPermutations) : FixedKeyOracle where
  hashToField label := (hashBytes permutations label).toNat
  encrypt label message := padBytes permutations label ^^^ fieldBytes message
  decrypt label row := (payload (padBytes permutations label) ^^^ row).toNat
  decryptEncrypt label message := by
    simp only [payload, BitVec.setWidth_xor]
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    simp only [fieldBytes, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by decide : coordinateBitCount ≤ 256)),
      Nat.mod_eq_of_lt]
    · exact ZMod.natCast_zmod_val message
    · exact lt_trans message.val_lt (by decide)

/-- A group MAC key encodes `b` as `slope * b + offset`. -/
structure OutputKey where
  slope : BaseField
  offset : BaseField

def OutputKey.encode (key : OutputKey) (value : Bool) : BaseField :=
  if value then key.slope + key.offset else key.offset

/-- The table stores only the row for the input value `true`. -/
structure Table where
  trueRow : Ciphertext

def garble (oracle : FixedKeyOracle) (slope : BaseField) (key : Key) :
    Table × OutputKey :=
  let outputKey : OutputKey := { slope, offset := oracle.hashToField key.falseLabel }
  ({ trueRow := oracle.encrypt key.trueLabel (outputKey.encode true) }, outputKey)

def evaluate (oracle : FixedKeyOracle) (table : Table) (value : Bool)
    (input : Block) : BaseField :=
  if value then oracle.decrypt input (payload table.trueRow) else oracle.hashToField input

theorem evaluateEncode (oracle : FixedKeyOracle) (slope : BaseField)
    (key : Key) (value : Bool) :
    evaluate oracle (garble oracle slope key).1 value (encode key value) =
      (garble oracle slope key).2.encode value := by
  cases value <;> simp [evaluate, garble, encode, OutputKey.encode]
  exact oracle.decryptEncrypt key.trueLabel (slope + oracle.hashToField key.falseLabel)

end Kriterion.ArgoMAC.BitAdaptor
