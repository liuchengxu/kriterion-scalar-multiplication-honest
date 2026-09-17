import Proof.Privacy.Distribution.CircuitHashDistribution
import Proof.Privacy.Distribution.OutputRowDistribution
import Proof.Privacy.Programming.ActualGateConstraints

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac

noncomputable section

/-- These arrays contain the actual X/Y/Z field randomizers. -/
abbrev RowMaskRandomizers := (Fin 4 → BaseField) × (Fin 3 → BaseField) × (Fin 4 → BaseField)

/-- This equivalence separates rho from the actual field randomizers. -/
def rowMaskRandomizerEquiv : RowRandomness ≃ NonZeroBase × RowMaskRandomizers where
  toFun row := (row.rho, ![row.x.r1, row.x.r2, row.x.r3, row.x.r5],
    ![row.y.r1, row.y.r4, row.y.r5], ![row.z.r2, row.z.r3, row.z.r4, row.z.r5])
  invFun pair := ⟨pair.1, ⟨pair.2.1 0, pair.2.1 1, pair.2.1 2, pair.2.1 3⟩,
    ⟨pair.2.2.1 0, pair.2.2.1 1, pair.2.2.1 2⟩,
    ⟨pair.2.2.2 0, pair.2.2.2 1, pair.2.2.2 2, pair.2.2.2 3⟩⟩
  left_inv row := by rcases row with ⟨rho, ⟨_, _, _, _⟩, ⟨_, _, _⟩, ⟨_, _, _, _⟩⟩; rfl
  right_inv pair := by
    refine Prod.ext rfl ?_
    apply Prod.ext
    · funext index; fin_cases index <;> rfl
    · apply Prod.ext <;> funext index <;> fin_cases index <;> rfl

/-- This equivalence keeps the scales and field randomizers of every actual row. -/
def pointMaskRandomizerEquiv : Randomness ≃
    (Fin outputMacCount → NonZeroBase) × (Fin outputMacCount → RowMaskRandomizers) where
  toFun rows := ((fun index => (rowMaskRandomizerEquiv (rows.get index)).1),
    fun index => (rowMaskRandomizerEquiv (rows.get index)).2)
  invFun pair := Vector.ofFn fun index => rowMaskRandomizerEquiv.symm (pair.1 index, pair.2 index)
  left_inv rows := by
    apply Vector.ext
    intro index valid
    simpa only [Vector.getElem_ofFn, Prod.eta, Vector.get, Fin.cast, Vector.getElem_toArray] using
      rowMaskRandomizerEquiv.symm_apply_apply (rows.get ⟨index, valid⟩)
  right_inv pair := by
    simp only [Vector.get_ofFn, Equiv.apply_symm_apply]

/-- This tape keeps the offsets, rho values, bridge key, curve mask, and actual oracle coin. -/
abbrev MaskRetainedTape [FieldCertificate] [GroupCertificate] :=
  ClampedAffineOffsets × (Fin outputMacCount → NonZeroBase) ×
    (BaseField × NonZeroBase) × GarblingOracleData

/-- This tape contains the curve and point randomizers that move into the mask source. -/
abbrev CircuitMaskRandomizers := (Fin 2 → BaseField) × (Fin outputMacCount → RowMaskRandomizers)

/-- This split moves each actual randomizer exactly once. -/
def maskRandomizerTapeEquiv [FieldCertificate] [GroupCertificate] :
    Garbling.Randomness ≃ MaskRetainedTape × CircuitMaskRandomizers :=
  garblingRandomnessOffsetEquiv.trans {
    toFun := fun sample =>
      ((sample.1, (pointMaskRandomizerEquiv sample.2.1).1,
        (sample.2.2.1.bridgeKey, sample.2.2.1.curveMask), sample.2.2.2),
      ![sample.2.2.1.curveR1, sample.2.2.1.curveR2], (pointMaskRandomizerEquiv sample.2.1).2)
    invFun := fun sample =>
      (sample.1.1, pointMaskRandomizerEquiv.symm (sample.1.2.1, sample.2.2),
        ⟨sample.1.2.2.1.1, sample.1.2.2.1.2, sample.2.1 0, sample.2.1 1⟩, sample.1.2.2.2)
    left_inv := by
      rintro ⟨offsets, rows, ⟨bridge, mask, r1, r2⟩, oracles⟩
      change (offsets, pointMaskRandomizerEquiv.symm (pointMaskRandomizerEquiv rows),
        (⟨bridge, mask, r1, r2⟩ : GarblingFieldData), oracles) = _
      rw [Equiv.symm_apply_apply]
    right_inv := by
      rintro ⟨⟨offsets, rho, ⟨bridge, mask⟩, oracles⟩, curve, rows⟩
      simp only [Equiv.apply_symm_apply]
      refine Prod.ext rfl ?_
      apply Prod.ext
      · funext index; fin_cases index <;> rfl
      · rfl }

/-- This view drops only the randomizers that the source already contains. -/
def maskRetainedTape [FieldCertificate] [GroupCertificate] (randomness : Garbling.Randomness) :
    MaskRetainedTape := (maskRandomizerTapeEquiv randomness).1

/-- This tape contains only the actual public ciphertext rows. -/
abbrev CircuitMaskTables := (Fin 5 → Vector BitAdaptor.Table coordinateBitCount) ×
  (Fin outputMacCount → (Fin 4 → Vector BitAdaptor.Table coordinateBitCount) ×
    (Fin 3 → Vector BitAdaptor.Table coordinateBitCount) ×
    (Fin 5 → Vector BitAdaptor.Table coordinateBitCount))

/-- This equivalence joins the field randomizers to their public tables. -/
def circuitHashRestEquiv : CircuitMaskRandomizers × CircuitMaskTables ≃ CircuitHashRest where
  toFun pair := ((pair.1.1, pair.2.1), fun row =>
    (((pair.1.2 row).1, (pair.2.2 row).1),
    ((pair.1.2 row).2.1, (pair.2.2 row).2.1),
    ((pair.1.2 row).2.2, (pair.2.2 row).2.2)))
  invFun rest := ((rest.1.1, fun row =>
    ((rest.2 row).1.1, (rest.2 row).2.1.1, (rest.2 row).2.2.1)),
    rest.1.2, fun row => ((rest.2 row).1.2, (rest.2 row).2.1.2, (rest.2 row).2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- This source rest uses the same field randomizers as the actual tape. -/
def sharedCircuitHashRest [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (tables : CircuitMaskTables) : CircuitHashRest :=
  circuitHashRestEquiv ((maskRandomizerTapeEquiv randomness).2, tables)

/-- This sample shares every randomizer with the actual tape. -/
def sharedCircuitMaskSample [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (hash : RawCircuitGate → BaseField × HashLiftQuotient)
    (tables : CircuitMaskTables) : CircuitMaskSample :=
  circuitMaskHashSplitEquiv.symm (hash, sharedCircuitHashRest randomness tables)

/-- The source satisfies the exact randomizer premise of the actual gate event. -/
theorem sharedCircuitMaskSample_randomizers [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (hash : RawCircuitGate → BaseField × HashLiftQuotient)
    (tables : CircuitMaskTables) :
    CircuitSourceRandomizers (sharedCircuitMaskSample randomness hash tables)
      randomness.pointRandomness randomness.curveR1 randomness.curveR2 := by
  exact ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- The source has the prescribed field residue at every actual bit gate. -/
theorem sharedCircuitMaskSample_field [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (hash : RawCircuitGate → BaseField × HashLiftQuotient)
    (tables : CircuitMaskTables) (gate : RawCircuitGate) :
    circuitSourceField (sharedCircuitMaskSample randomness hash tables) gate = (hash gate).1 := by
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · rfl
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> rfl

/-- The shared source has the residue of its actual complete-fiber hash lift. -/
theorem sharedCircuitMaskSample_residues [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) (hash : RawCircuitGate → BaseField × HashLiftQuotient)
    (tables : CircuitMaskTables) (gate : RawCircuitGate) :
    circuitSourceField (sharedCircuitMaskSample randomness hash tables) gate =
      ((goodHashLiftSource (hash gate)).val : BaseField) := by
  rw [sharedCircuitMaskSample_field, goodHashLiftSource_eq]
  change (hash gate).1 = ((goodHashLift (hash gate).1 (hash gate).2).1.toNat : BaseField)
  rw [goodHashLift_toNat]
  have residue := goodHashLiftEquiv_fst (goodHashLiftEquiv.symm (hash gate))
  rw [Equiv.apply_symm_apply] at residue
  exact residue

/-- The retained tape determines every mathematical output row. -/
theorem maskRetainedTape_same_rows [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (first second : Garbling.Randomness)
    (same : maskRetainedTape first = maskRetainedTape second) :
    rowsForOutputKeys (outputKeys construction scalar first.offsets) first.pointRandomness =
      rowsForOutputKeys (outputKeys construction scalar second.offsets) second.pointRandomness := by
  have offsets : first.offsets = second.offsets := congrArg (fun tape => tape.1.1) same
  have scales : (fun index => (first.pointRandomness.get index).rho) =
      (fun index => (second.pointRandomness.get index).rho) :=
    congrArg (fun tape => tape.2.1) same
  apply Vector.ext
  intro index valid
  simp only [rowsForOutputKeys, Vector.getElem_ofFn, offsets, congrFun scales]

/-- This equivalence retains an arbitrary hash tape while moving the shared randomizers. -/
def sharedHashSourceEquiv [FieldCertificate] [GroupCertificate] (Hash : Type*) :
    (Garbling.Randomness × Hash × CircuitMaskTables) ≃ MaskRetainedTape × Hash × CircuitHashRest :=
  (Equiv.prodCongr maskRandomizerTapeEquiv (Equiv.refl _)).trans {
    toFun := fun sample => (sample.1.1, sample.2.1,
      circuitHashRestEquiv (sample.1.2, sample.2.2))
    invFun := fun sample => ((sample.1, (circuitHashRestEquiv.symm sample.2.2).1),
      sample.2.1, (circuitHashRestEquiv.symm sample.2.2).2)
    left_inv := by
      rintro ⟨⟨retained, randomizers⟩, hash, tables⟩
      simp only [Equiv.symm_apply_apply]
    right_inv := by
      rintro ⟨retained, hash, rest⟩
      change (retained, hash, circuitHashRestEquiv (circuitHashRestEquiv.symm rest)) = _
      rw [Equiv.apply_symm_apply] }

/-- This equivalence gives the independent mask source after the correct tape projection. -/
def sharedMaskSourceEquiv [FieldCertificate] [GroupCertificate] :
    (Garbling.Randomness × (RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables) ≃
      MaskRetainedTape × CircuitMaskSample :=
  (sharedHashSourceEquiv _).trans
    (Equiv.prodCongr (Equiv.refl _) circuitMaskHashSplitEquiv.symm)

attribute [local instance] vectorFintype rowRandomnessFintype
  xRandomnessFintype yRandomnessFintype zRandomnessFintype bitAdaptorTableFintype
  circuitMaskSampleFintype

instance maskRetainedTapeNonempty [FieldCertificate] [GroupCertificate] : Nonempty MaskRetainedTape :=
  ⟨maskRetainedTape (Seed.randomness 0)⟩

instance circuitMaskTablesNonempty : Nonempty CircuitMaskTables :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ => ((fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
      (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
      (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable))⟩

local instance {count : Nat} : Nonempty (BiquadraticSampleRemainder count) :=
  ⟨(fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable,
    fun _ _ => defaultHashLiftQuotient)⟩

local instance : Nonempty CircuitHashRest :=
  ⟨circuitHashRestEquiv ((0, fun _ => (0, 0, 0)), Classical.arbitrary CircuitMaskTables)⟩

local instance : Fintype RawCircuitGate := inferInstance
local instance : DecidableEq RawCircuitGate := Classical.decEq _
local instance : Fintype CircuitMaskTables := inferInstance
local instance : Fintype CircuitHashRest := inferInstance


/-- The projected actual tape has the exact independent uniform law. -/
theorem map_randomTape_maskRetained [FieldCertificate] [GroupCertificate]
    (witness : Garbling.Randomness) (parameter : Nat) :
    (randomTape witness parameter).map maskRetainedTape = PMF.uniformOfFintype MaskRetainedTape := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  change (PMF.uniformOfFintype Garbling.Randomness).map (Prod.fst ∘ maskRandomizerTapeEquiv) = _
  rw [← PMF.map_comp, map_uniformOfFintype_equivBetween maskRandomizerTapeEquiv,
    map_uniform_prod_fst]

/-- The shared mask source and the independent mask hybrid have the same projected observation. -/
theorem sharedMaskSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Observation : Type*} (witness : Garbling.Randomness) (parameter : Nat)
    (observe : MaskRetainedTape → CircuitMaskSample → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype
        ((RawCircuitGate → BaseField × HashLiftQuotient) × CircuitMaskTables)).bind fun source =>
          observe (maskRetainedTape randomness)
            (sharedCircuitMaskSample randomness source.1 source.2)) =
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype CircuitMaskSample).bind fun source =>
        observe (maskRetainedTape randomness) source) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  have law := congrArg (fun distribution => distribution.bind
    (fun source : MaskRetainedTape × CircuitMaskSample => observe source.1 source.2))
    (map_uniformOfFintype_equivBetween sharedMaskSourceEquiv)
  rw [PMF.bind_map, uniform_product_bind (A := Garbling.Randomness),
    uniform_product_bind (A := MaskRetainedTape)] at law
  have retained := congrArg (fun distribution => distribution.bind
    (fun value => (PMF.uniformOfFintype CircuitMaskSample).bind (observe value)))
    (map_randomTape_maskRetained witness parameter)
  rw [PMF.bind_map] at retained
  dsimp only [Function.comp_def] at law retained
  exact law.trans retained.symm

/-- The full hash source also has an exact shared-randomizer disintegration. -/
theorem sharedHashSource_observation_eq [FieldCertificate] [GroupCertificate]
    {Hash Observation : Type*} [Fintype Hash] [Nonempty Hash]
    (witness : Garbling.Randomness) (parameter : Nat)
    (observe : MaskRetainedTape → Hash × CircuitHashRest → PMF Observation) :
    (randomTape witness parameter).bind (fun randomness =>
      (PMF.uniformOfFintype (Hash × CircuitMaskTables)).bind fun source =>
        observe (maskRetainedTape randomness) (source.1, sharedCircuitHashRest randomness source.2)) =
    (PMF.uniformOfFintype (Hash × CircuitHashRest)).bind (fun source =>
      (PMF.uniformOfFintype MaskRetainedTape).bind fun retained => observe retained source) := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  have law := congrArg (fun distribution => distribution.bind
    (fun source : MaskRetainedTape × Hash × CircuitHashRest => observe source.1 source.2))
    (map_uniformOfFintype_equivBetween (sharedHashSourceEquiv Hash))
  rw [PMF.bind_map, uniform_product_bind (A := Garbling.Randomness),
    uniform_product_bind (A := MaskRetainedTape)] at law
  conv_rhs at law => rw [PMF.bind_comm]
  exact law

end

end Kriterion.ArgoMAC.Security
