import Proof.Privacy.Source.RealSourceLower
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section

/-- The retained row reconstruction gives the exact original output-key rows. -/
theorem retainedSourceRows_randomness [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (randomness : Garbling.Randomness) :
    retainedSourceRows scalar (maskRetainedTape randomness) =
      rowsForOutputKeys (outputKeys construction scalar randomness.offsets) randomness.pointRandomness := by
  apply maskRetainedTape_same_rows scalar
    (retainedSourceTape (maskRetainedTape randomness)) randomness
  change (maskRandomizerTapeEquiv (maskRandomizerTapeEquiv.symm
    (maskRetainedTape randomness, (0, fun _ => (0, 0, 0))))).1 = _
  rw [Equiv.apply_symm_apply]

/-- The oracle and input-key split keeps every shared source randomizer. -/
theorem sharedCircuitHashRest_oracleKey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (tables : CircuitMaskTables) :
    sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tables =
      sharedCircuitHashRest rest.reference tables := rfl

/-- The oracle and input-key split keeps the actual retained row family. -/
theorem retainedSourceRows_oracleKey [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) :
    retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))) =
      rowsForOutputKeys (outputKeys construction scalar rest.reference.offsets)
        rest.algebraic.point.pointRandomness := by
  rw [retainedSourceRows_randomness]
  rfl

/-- The retained real tag table is the exact table used by the full source prefix. -/
theorem retainedFullTable_prefixTable [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
    (tag : FullCircuitSource) :
    retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag =
      circuitMaskSourceTable
        (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.1
        (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape (garblingOracleKeyEquiv.symm (sample, rest))))
        (decodeFullSource (tag.1, sharedCircuitHashRest (garblingOracleKeyEquiv.symm (sample, rest)) tag.2)) := by
  rw [retainedSourceRows_oracleKey, sharedCircuitHashRest_oracleKey]
  rfl

end
end Kriterion.ArgoMAC.Security
