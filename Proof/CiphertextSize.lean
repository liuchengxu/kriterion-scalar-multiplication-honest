import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Wire

open BN254

/-- Every garbling has the declared ciphertext size. The encoder writes the
packed table, so the transmitted value is the packed garble. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    (encoding.encode
      (Pipeline.Table.pack
        ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1)).length =
      8887896 := by
  rw [show ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1 =
    (Garbling.garble construction scalar randomness).1 from rfl]
  exact garble_length construction scalar randomness

end Kriterion.ArgoMAC.Wire
