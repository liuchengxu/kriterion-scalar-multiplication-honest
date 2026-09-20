import Proof.Privacy.Source.RetainedTableAlignment
import Proof.Privacy.Source.SharedRandomnessSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
noncomputable section

/-- The shared oracle split keeps all source randomizers. -/
theorem sharedCircuitHashRest_sharedOracleKey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (tables : CircuitMaskTables) :
    sharedCircuitHashRest (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val tables =
      sharedCircuitHashRest rest.reference tables := rfl

/-- The shared oracle split keeps the exact retained row family. -/
theorem retainedSourceRows_sharedOracleKey [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :
    retainedSourceRows scalar (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val) =
      rowsForOutputKeys (outputKeys construction scalar rest.reference.offsets)
        rest.algebraic.point.pointRandomness :=
  retainedSourceRows_oracleKey scalar rest (Shared.expandOracle sample.1, sample.2)

/-- The retained full table is the exact shared prefix table. -/
theorem retainedFullTable_sharedPrefixTable [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (rest : GarblingSourceRest)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) (tag : FullCircuitSource) :
    retainedFullTable rest (outputKeys construction scalar rest.reference.offsets) tag =
      circuitMaskSourceTable
        (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.1.1
        (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.1.2.value
        (retainedSourceRows scalar (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val))
        (decodeFullSource (tag.1, sharedCircuitHashRest (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val tag.2)) :=
  retainedFullTable_prefixTable scalar rest (Shared.expandOracle sample.1, sample.2) tag

/-- The shared tape split preserves the complete source oracle data. -/
theorem maskRetainedTape_sharedOracleKey_data [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :
    (maskRetainedTape (sharedGarblingOracleKeyEquiv.symm (sample, rest)).val).2.2.2 =
      (⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ : GarblingOracleData) := rfl

end
end Kriterion.ArgoMAC.Security
