import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Wire

open BN254

-- The packed adaptor encoding is 8,065 bytes, so the kernel walks that many
-- constructors when it checks a length.
set_option maxRecDepth 100000

/-- Every garbling has the declared ciphertext size. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    (encoding.encode
      (Lamport.packedCircuit.garble parameter scalar randomness).1).length =
      8891172 := by
  dsimp only [Lamport.packedCircuit, Lamport.wireCircuit, GarbledCircuit.mapPublic,
    GarbledCircuit.mapLabels, Garbling.garbledCircuit]
  have size := garble_length construction scalar randomness
  simpa only [Garbling.PublicCircuit] using size

end Kriterion.ArgoMAC.Wire
