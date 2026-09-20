import Proof.Privacy.Source.SharedFullSourceTape
import Proof.Privacy.Distribution.MaskRandomizerDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype bitAdaptorTableFintype
  circuitMaskSampleFintype instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

local instance sharedMaskRemainderNonempty {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

/-- The shared tape splits its randomizers without changing the fixed oracle. -/
def actualSharedMaskTapeEquiv [FieldCertificate] [GroupCertificate] :
    Shared.Randomness ≃ SharedMaskRetainedTape × CircuitMaskRandomizers :=
  (maskRandomizerTapeEquiv.subtypeEquiv
    (p := fun tape => Shared.expandOracle (Shared.restrictOracle tape.fixedKeyOracle) = tape.fixedKeyOracle)
    (q := fun pair => Shared.expandOracle (Shared.restrictOracle pair.1.2.2.2.fixedKeyOracle) = pair.1.2.2.2.fixedKeyOracle)
    (fun _ => Iff.rfl)).trans
    (Equiv.prodSubtypeFstEquivSubtypeProd (α := MaskRetainedTape) (β := CircuitMaskRandomizers)
      (p := fun retained => Shared.expandOracle (Shared.restrictOracle retained.2.2.2.fixedKeyOracle) = retained.2.2.2.fixedKeyOracle))

instance actualSharedMaskRetainedNonempty [FieldCertificate] [GroupCertificate] : Nonempty SharedMaskRetainedTape :=
  ⟨sharedMaskRetainedTape (Shared.Randomness.ofLegacy (Seed.randomness 0))⟩

/-- The shared hash-source equivalence keeps the exact three-slot oracle constraint. -/
def actualSharedHashSourceEquiv [FieldCertificate] [GroupCertificate] (Hash : Type*) :
    (Shared.Randomness × Hash × CircuitMaskTables) ≃ SharedMaskRetainedTape × Hash × CircuitHashRest :=
  (Equiv.prodSubtypeFstEquivSubtypeProd (α := Garbling.Randomness) (β := Hash × CircuitMaskTables)
    (p := fun tape => Shared.expandOracle (Shared.restrictOracle tape.fixedKeyOracle) = tape.fixedKeyOracle)).symm.trans
    (((sharedHashSourceEquiv Hash).subtypeEquiv
      (p := fun pair => Shared.expandOracle (Shared.restrictOracle pair.1.fixedKeyOracle) = pair.1.fixedKeyOracle)
      (q := fun pair => Shared.expandOracle (Shared.restrictOracle pair.1.2.2.2.fixedKeyOracle) = pair.1.2.2.2.fixedKeyOracle)
      (fun _ => Iff.rfl)).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (α := MaskRetainedTape) (β := Hash × CircuitHashRest)
        (p := fun retained => Shared.expandOracle (Shared.restrictOracle retained.2.2.2.fixedKeyOracle) = retained.2.2.2.fixedKeyOracle)))

/-- The independent mask source keeps the actual shared retained tape. -/
def actualSharedMaskSourceEquiv [FieldCertificate] [GroupCertificate] :
    (Shared.Randomness × (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables) ≃
      SharedMaskRetainedTape × CircuitMaskSample :=
  (actualSharedHashSourceEquiv _).trans
    (Equiv.prodCongr (Equiv.refl _) circuitMaskHashSplitEquiv.symm)

/-- The lifted mask source keeps the original deterministic projections. -/
theorem actualSharedMaskSourceEquiv_apply [FieldCertificate] [GroupCertificate]
    (tape : Shared.Randomness)
    (source : (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables) :
    actualSharedMaskSourceEquiv (tape, source) =
      (sharedMaskRetainedTape tape, sharedCircuitMaskSample tape.val source.1 source.2) := rfl

/-- The projected shared tape has the exact uniform retained law. -/
theorem map_sharedRandomTape_maskRetained [FieldCertificate] [GroupCertificate]
    (witness : Shared.Randomness) (parameter : Nat) :
    (uniformRandomTape Shared.Randomness witness parameter).map sharedMaskRetainedTape =
      PMF.uniformOfFintype SharedMaskRetainedTape := by
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  rw [uniformRandomTape, uniformTape_eq]
  change (PMF.uniformOfFintype Shared.Randomness).map (Prod.fst ∘ actualSharedMaskTapeEquiv) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween actualSharedMaskTapeEquiv, map_uniform_prod_fst]

/-- The shared actual source and the independent mask source have the same observation law. -/
theorem actualSharedMaskSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (witness : Shared.Randomness) (parameter : Nat)
    (observe : SharedMaskRetainedTape → CircuitMaskSample → PMF Observation) :
    (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          observe (sharedMaskRetainedTape randomness)
            (sharedCircuitMaskSample randomness.val source.1 source.2)) =
    (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
        observe (sharedMaskRetainedTape randomness) source) := by
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  have law := congrArg (fun distribution => distribution.bind
    (fun source : SharedMaskRetainedTape × CircuitMaskSample => observe source.1 source.2))
    (map_uniformOfFintype_equivBetween actualSharedMaskSourceEquiv)
  rw [PMF.bind_map, uniform_product_bind (A := Shared.Randomness),
    uniform_product_bind (A := SharedMaskRetainedTape)] at law
  have retained := congrArg (fun distribution => distribution.bind
    (fun value => (PMF.uniformOfFintype CircuitMaskSample).bind (observe value)))
    (map_sharedRandomTape_maskRetained witness parameter)
  rw [PMF.bind_map] at retained
  dsimp only [Function.comp_def] at law retained
  simp only [actualSharedMaskSourceEquiv_apply] at law
  rw [uniformRandomTape, uniformTape_eq] at retained ⊢
  exact law.trans retained.symm

/-- The lifted hash source keeps the original deterministic projections. -/
theorem actualSharedHashSourceEquiv_apply [FieldCertificate] [GroupCertificate]
    {Hash : Type*} (tape : Shared.Randomness) (source : Hash × CircuitMaskTables) :
    actualSharedHashSourceEquiv Hash (tape, source) =
      (sharedMaskRetainedTape tape, source.1, sharedCircuitHashRest tape.val source.2) := rfl

/-- The shared hash source has the exact independent retained law. -/
theorem actualSharedHashSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Hash Observation : Type*} [Fintype Hash] [Nonempty Hash]
    (witness : Shared.Randomness) (parameter : Nat)
    (observe : SharedMaskRetainedTape → Hash × CircuitHashRest → PMF Observation) :
    (uniformRandomTape Shared.Randomness witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype (Hash × CircuitMaskTables)).bind fun source =>
        observe (sharedMaskRetainedTape randomness)
          (source.1, sharedCircuitHashRest randomness.val source.2)) =
    (PMF.uniformOfFintype SharedMaskRetainedTape).bind (fun retained =>
      (PMF.uniformOfFintype (Hash × CircuitHashRest)).bind (observe retained)) := by
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  have law := congrArg (fun distribution => distribution.bind
    (fun source : SharedMaskRetainedTape × Hash × CircuitHashRest => observe source.1 source.2))
    (map_uniformOfFintype_equivBetween (actualSharedHashSourceEquiv Hash))
  rw [PMF.bind_map, uniform_product_bind (A := Shared.Randomness),
    uniform_product_bind (A := SharedMaskRetainedTape)] at law
  simp only [Function.comp_def, actualSharedHashSourceEquiv_apply] at law
  rw [uniformRandomTape, uniformTape_eq]
  exact law

end
end Kriterion.ArgoMAC.Security
