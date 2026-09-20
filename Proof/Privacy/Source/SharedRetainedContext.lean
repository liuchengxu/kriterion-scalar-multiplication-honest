import Proof.Privacy.Source.SharedContextActual
import Proof.Privacy.Source.RealSourceLower

namespace Kriterion.ArgoMAC.Security.SharedRetained
open BN254 Cryptography
noncomputable section

/-- This context keeps the actual output rows and the complete source tag. -/
def retainedSourceContext [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (key : InputMacKey) :
    Context × HiddenPublicSample :=
  actualSourceContext rest.oracleCoin rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
    input (retainedFullSource rest tag) key

/-- The retained context uses the actual encryption links. -/
theorem retainedSourceContext_linked [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (key : InputMacKey) :
    (retainedSourceContext rest keys input tag key).1.Linked rest.oracleCoin rest.algebraic.field.bridgeKey :=
  actualSourceContext_linked _ _ _ _ _ _ _

/-- The retained context reconstructs the actual input key. -/
theorem retainedSourceContext_key [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (key : InputMacKey) :
    (retainedSourceContext rest keys input tag key).1.curveKey
      (fun index => inputKeyLabel key index (!(inputSelectedLabelBit input index))) = key :=
  actualSourceContext_key _ _ _ _ _ _ _

/-- The retained context reconstructs the source from the complete tag. -/
theorem retainedSourceContext_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (key : InputMacKey) :
    let retained := retainedSourceContext rest keys input tag key
    retained.1.source retained.2 = retainedFullSource rest tag :=
  actualSourceContext_source _ _ _ _ (FieldMacToECMac.rowsForOutputKeysSparse _ _) _ _ _

/-- The retained context recovers every complete hash lift in the tag. -/
theorem retainedSourceContext_lifts [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (key : InputMacKey) :
    let retained := retainedSourceContext rest keys input tag key
    retained.1.lifts retained.2 = tag.1 := by
  exact (actualSourceContext_lifts _ _ _ _
    (FieldMacToECMac.rowsForOutputKeysSparse _ _) _ _ _).trans (retainedFullSource_lifts rest tag complete)

/-- The retained context recovers the complete tag used by the global source sum. -/
theorem retainedSourceContext_tag [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (key : InputMacKey) :
    let retained := retainedSourceContext rest keys input tag key
    (retained.1.lifts retained.2, sourceCiphertexts (retained.1.source retained.2)) = tag := by
  dsimp only
  rw [retainedSourceContext_lifts rest keys input tag complete key,
    retainedSourceContext_source, retainedFullSource_ciphertexts]

end
end Kriterion.ArgoMAC.Security.SharedRetained
