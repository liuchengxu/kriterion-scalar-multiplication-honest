import Proof.Privacy.Distribution.SharedOutputEquiv

namespace Kriterion.ArgoMAC.Security
open BN254 FieldMacToECMac
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype xRandomnessFintype
  yRandomnessFintype zRandomnessFintype

/-- The output rest retains the exact shared fixed oracle. -/
abbrev SharedOutputRowRest := {rest : OutputRowRest //
  Shared.expandOracle (Shared.restrictOracle rest.2.2.fixedKeyOracle) = rest.2.2.fixedKeyOracle}

/-- The shared output source separates the actual online coin. -/
def sharedOutputEncodingSourceEquiv [FieldCertificate] :
    SharedOutputRowSource ≃ SharedOutputRowRest × ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase)) :=
  (((outputEncodingSourceEquiv.trans (Equiv.prodComm _ _)).subtypeEquiv
    (p := fun source => Shared.expandOracle (Shared.restrictOracle source.2.2.2.2.fixedKeyOracle) =
      source.2.2.2.2.fixedKeyOracle)
    (q := fun pair => Shared.expandOracle (Shared.restrictOracle pair.1.2.2.fixedKeyOracle) =
      pair.1.2.2.fixedKeyOracle) (fun _ => Iff.rfl))).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (α := OutputRowRest)
      (β := (Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))
      (p := fun rest => Shared.expandOracle (Shared.restrictOracle rest.2.2.fixedKeyOracle) = rest.2.2.fixedKeyOracle))

instance sharedOutputRowRestNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedOutputRowRest :=
  Nonempty.map (fun source : SharedOutputRowSource => (sharedOutputEncodingSourceEquiv source).1) inferInstance

/-- The shared output law uses the exact free-point and scale coin after the input choice. -/
theorem sharedIdealOutput_encodingSource [FieldCertificate] [GroupCertificate]
    {Aux Observation : Type*} (scalar : ScalarField)
    (choose : OutputRowRest → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → Option Result → OutputRowRest → PMF Observation) :
    (PMF.uniformOfFintype SharedOutputRowSource).bind (fun source =>
      (choose source.val.2.2).bind (fun selected =>
        observe selected (idealSelectedOutput scalar selected.1 source.val) source.val.2.2)) =
    (PMF.uniformOfFintype SharedOutputRowRest).bind (fun rest =>
      (choose rest.val).bind (fun selected =>
        (PMF.uniformOfFintype
          ((Fin 90 → Point) × (Fin outputMacCount → NonZeroBase))).bind fun coin =>
          observe selected ((decodePoint selected.1).map fun point =>
            ⟨selected.1, outputTargets (scalarMultiplication scalar point)
              (Vector.ofFn coin.1) coin.2⟩) rest.val)) := by
  have source := map_uniformOfFintype_equivBetween sharedOutputEncodingSourceEquiv.symm
  rw [← source, PMF.bind_map, uniform_product_bind (A := SharedOutputRowRest)]
  apply congrArg ((PMF.uniformOfFintype SharedOutputRowRest).bind)
  funext rest
  rw [PMF.bind_comm]
  rfl

end
end Kriterion.ArgoMAC.Security
