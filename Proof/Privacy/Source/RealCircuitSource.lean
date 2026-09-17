import Proof.Privacy.Distribution.MaskRandomizerDistribution
import Proof.Privacy.Transcript.AdaptiveGameRatio

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography FieldMacToECMac

noncomputable section

/-- This equivalence lists each public ciphertext at its actual circuit gate. -/
def circuitMaskTablesEquiv : CircuitMaskTables ≃ (RawCircuitGate → BitAdaptor.Table) where
  toFun tables gate := match gate with
    | .inl (adaptor, bit) => (tables.1 adaptor).get bit
    | .inr (row, .inl (adaptor, bit)) => ((tables.2 row).1 adaptor).get bit
    | .inr (row, .inr (.inl (adaptor, bit))) => ((tables.2 row).2.1 adaptor).get bit
    | .inr (row, .inr (.inr (adaptor, bit))) => ((tables.2 row).2.2 adaptor).get bit
  invFun tables := (
    fun adaptor => Vector.ofFn fun bit => tables (.inl (adaptor, bit)),
    fun row => (
      fun adaptor => Vector.ofFn fun bit => tables (.inr (row, .inl (adaptor, bit))),
      fun adaptor => Vector.ofFn fun bit => tables (.inr (row, .inr (.inl (adaptor, bit)))),
      fun adaptor => Vector.ofFn fun bit => tables (.inr (row, .inr (.inr (adaptor, bit))))))
  left_inv tables := by
    apply Prod.ext
    · funext adaptor
      apply Vector.ext
      intro index valid
      simp only [Vector.getElem_ofFn]
      rfl
    · funext row
      apply Prod.ext
      · funext adaptor
        apply Vector.ext
        intro index valid
        simp only [Vector.getElem_ofFn]
        rfl
      · apply Prod.ext <;> funext adaptor <;> apply Vector.ext <;> intro index valid <;> simp only [Vector.getElem_ofFn] <;> rfl
  right_inv tables := by
    funext gate
    rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
    · simp only [Vector.get_ofFn]
    · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> simp only [Vector.get_ofFn]

/-- This tag contains every actual full hash and ciphertext. It contains no key. -/
abbrev FullCircuitSource := (RawCircuitGate → FullHashLift) × CircuitMaskTables

/-- This function reads the actual false-label hash tape. -/
def actualCircuitHashTape (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (pointKey inputKey : InputMacKey) : RawCircuitGate → FullHashLift :=
  fun gate => fixedDaviesMeyerHashLift (rawCircuitLocation gate) (rawCircuitWindow gate)
    (circuitGateKey pointKey inputKey gate).falseLabel oracle

/-- This function extracts only the ciphertexts from the actual public table. -/
def pipelineCiphertexts (table : Pipeline.Table) : CircuitMaskTables :=
  circuitMaskTablesEquiv.symm (pipelineGateTable table)

/-- This projection removes the field randomizers and retains every source ciphertext. -/
def sourceCiphertexts (source : CircuitMaskSample) : CircuitMaskTables :=
  circuitMaskTablesEquiv.symm (circuitSourceTable source)

/-- This actual source tag leaves the key arguments inside the real experiment. -/
def actualFullCircuitSource (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) : FullCircuitSource :=
  let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
  (actualCircuitHashTape oracle pointKey inputKey,
    pipelineCiphertexts (Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2
      oracle encOracle hashOracle inputKey))

private theorem actualCiphertexts_source (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (quotients : CircuitMaskQuotients) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    circuitSourceTable (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask.value r1 r2
      oracle pointKey inputKey quotients) =
    pipelineGateTable (Pipeline.garble outputKeys pointRandomness bridgeKey mask r1 r2
      oracle encOracle hashOracle inputKey) := by
  dsimp only
  have assembled := actualCircuitMaskSample_pipelineTable outputKeys pointRandomness bridgeKey r1 r2 mask
    oracle encOracle hashOracle inputKey quotients (⟨0, 0⟩ : AffineInput)
  funext gate
  rw [← assembled]
  exact (circuitSourcePipelineTable_gate bridgeKey mask.value
    (rowsForOutputKeys outputKeys pointRandomness) (⟨0, 0⟩ : AffineInput) _ gate).symm

/-- The actual source fiber is exactly the full raw circuit constraint event. -/
theorem actualFullCircuitSource_fiber (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField)) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask
      oracle encOracle hashOracle inputKey = (lifts, sourceCiphertexts source) ↔
    RawGarblingMatches (sourceGatePrescription source pointKey inputKey lifts) oracle := by
  dsimp only
  let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
  let actual := actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask.value r1 r2
    oracle pointKey inputKey (circuitSourceQuotients source)
  have tables := actualCiphertexts_source outputKeys pointRandomness bridgeKey r1 r2 mask
    oracle encOracle hashOracle inputKey (circuitSourceQuotients source)
  rw [rawGarblingMatches_iff_actualSource outputKeys pointRandomness bridgeKey mask.value r1 r2
    oracle pointKey inputKey source lifts randomizers residues]
  change (actualCircuitHashTape oracle pointKey inputKey,
    circuitMaskTablesEquiv.symm (pipelineGateTable (Pipeline.garble outputKeys pointRandomness
      bridgeKey mask r1 r2 oracle encOracle hashOracle inputKey))) =
    (lifts, circuitMaskTablesEquiv.symm (circuitSourceTable source)) ↔
      CircuitHashMatches pointKey inputKey lifts oracle ∧ actual = source
  rw [Prod.mk.injEq, Equiv.apply_eq_iff_eq]
  constructor
  · rintro ⟨hashes, ciphertexts⟩
    have matched : CircuitHashMatches pointKey inputKey lifts oracle :=
      fun gate => congrFun hashes gate
    refine ⟨matched, circuitSource_ext ?_ ?_ rfl⟩
    · exact actualCircuitMaskSample_data_of_hash outputKeys pointRandomness bridgeKey mask.value r1 r2
        oracle pointKey inputKey source lifts randomizers residues matched
    · exact tables.trans ciphertexts
  · rintro ⟨hashes, equal⟩
    refine ⟨funext hashes, ?_⟩
    exact tables.symm.trans (congrArg circuitSourceTable equal)

/-- This source mass is the probability of the actual circuit constraints. -/
theorem actualFullCircuitSource_mass (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracles : PMF (PermutationOracle Pipeline.FixedKeyIndex Block))
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField)) :
    let pointKey := EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey
    (oracles.map (fun oracle => actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2
      mask oracle encOracle hashOracle inputKey)) (lifts, sourceCiphertexts source) =
    oracles.toOuterMeasure {oracle | RawGarblingMatches
      (sourceGatePrescription source pointKey inputKey lifts) oracle} := by
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext oracle
  exact actualFullCircuitSource_fiber outputKeys pointRandomness bridgeKey r1 r2 mask oracle
    encOracle hashOracle inputKey source lifts randomizers residues

/-- This tag permits an independent point key in the intermediate experiment. -/
def independentFullCircuitSource (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey mask r1 r2 : BaseField) (pointKey inputKey : InputMacKey)
    (quotients : CircuitMaskQuotients)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : FullCircuitSource :=
  (actualCircuitHashTape oracle pointKey inputKey,
    sourceCiphertexts (actualCircuitMaskSample outputKeys pointRandomness bridgeKey mask r1 r2
      oracle pointKey inputKey quotients))

/-- This fiber keeps both keys inside the intermediate experiment. -/
theorem independentFullCircuitSource_fiber (outputKeys : OutputKeys) (pointRandomness : Randomness)
    (bridgeKey mask r1 r2 : BaseField) (pointKey inputKey : InputMacKey)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField)) :
    independentFullCircuitSource outputKeys pointRandomness bridgeKey mask r1 r2 pointKey inputKey
      (circuitSourceQuotients source) oracle = (lifts, sourceCiphertexts source) ↔
    RawGarblingMatches (sourceGatePrescription source pointKey inputKey lifts) oracle := by
  rw [rawGarblingMatches_iff_actualSource outputKeys pointRandomness bridgeKey mask r1 r2
    oracle pointKey inputKey source lifts randomizers residues]
  change (actualCircuitHashTape oracle pointKey inputKey,
    circuitMaskTablesEquiv.symm (circuitSourceTable (actualCircuitMaskSample outputKeys
      pointRandomness bridgeKey mask r1 r2 oracle pointKey inputKey (circuitSourceQuotients source)))) =
      (lifts, circuitMaskTablesEquiv.symm (circuitSourceTable source)) ↔ _
  rw [Prod.mk.injEq, Equiv.apply_eq_iff_eq]
  constructor
  · rintro ⟨hashes, tables⟩
    have matched : CircuitHashMatches pointKey inputKey lifts oracle := fun gate => congrFun hashes gate
    exact ⟨matched, circuitSource_ext
      (actualCircuitMaskSample_data_of_hash outputKeys pointRandomness bridgeKey mask r1 r2
        oracle pointKey inputKey source lifts randomizers residues matched) tables rfl⟩
  · rintro ⟨hashes, equal⟩
    exact ⟨funext hashes, congrArg circuitSourceTable equal⟩

/-- The source tag does not depend on the auxiliary quotient tape. -/
theorem independentFullCircuitSource_quotients (outputKeys : OutputKeys)
    (pointRandomness : Randomness) (bridgeKey mask r1 r2 : BaseField)
    (pointKey inputKey : InputMacKey) (left right : CircuitMaskQuotients)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    independentFullCircuitSource outputKeys pointRandomness bridgeKey mask r1 r2 pointKey inputKey
      left oracle = independentFullCircuitSource outputKeys pointRandomness bridgeKey mask r1 r2
        pointKey inputKey right oracle := by
  apply Prod.ext
  · rfl
  · apply congrArg circuitMaskTablesEquiv.symm
    funext gate
    rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
    · rfl
    · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> rfl

/-- The linked intermediate tag equals the actual real source tag. -/
theorem independentFullCircuitSource_linked (outputKeys : OutputKeys)
    (pointRandomness : Randomness) (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encOracle : PermutationOracle EncPRF.PermutationIndex Block) (hashOracle : EncPRF.HashOracle)
    (inputKey : InputMacKey) (quotients : CircuitMaskQuotients) :
    independentFullCircuitSource outputKeys pointRandomness bridgeKey mask.value r1 r2
      (EncPRF.transformKey encOracle (EncPRF.whiteningKeys hashOracle bridgeKey) inputKey)
      inputKey quotients oracle =
    actualFullCircuitSource outputKeys pointRandomness bridgeKey r1 r2 mask oracle encOracle
      hashOracle inputKey := by
  apply Prod.ext
  · rfl
  · exact congrArg circuitMaskTablesEquiv.symm
      (actualCiphertexts_source outputKeys pointRandomness bridgeKey r1 r2 mask oracle encOracle
        hashOracle inputKey quotients)

end

end Kriterion.ArgoMAC.Security
