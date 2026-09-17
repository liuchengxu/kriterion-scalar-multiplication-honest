import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Wire

open BN254

-- The transmitted value is one 8,887,302-byte numeral. Unfolding the byte
-- encoding is never needed and never cheap: the length theorem is proved where
-- the encoding is defined.
attribute [local irreducible] Kriterion.ArgoMAC.Wire.encoding

set_option maxRecDepth 100000

/-- Every garbling has the declared ciphertext size. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    (encoding.encode
      (Lamport.packedCircuit.garble parameter scalar randomness).1).length =
      8887896 :=
  encoding_length _

end Kriterion.ArgoMAC.Wire
