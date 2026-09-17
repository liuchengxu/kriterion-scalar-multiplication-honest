import Proof.Privacy.Collision.PartialInactiveCount
import Proof.Privacy.Collision.AdaptiveLabelCollision
import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Each label bucket reads one coordinate index. -/
def circuitBucketWire (bucket : RawLabelBucket) : EncPRF.PermutationIndex :=
  match bucket.1 with
  | .curve .x3 | .curve .x5 | .curve .x7
  | .point _ .x7 | .point _ .x9 | .point .y .y6 => (.x, bucket.2)
  | .curve .y4 | .curve .y6 | .point .x .y6 | .point .z .y6
  | .point _ .y8 | .point _ .y10 => (.y, bucket.2)

/-- The source labels retain both actual input keys. -/
def circuitSourceLabels (curveKey pointKey : InputMacKey)
    (bucket : RawLabelBucket) (branch : Bool) : Block :=
  match bucket.1 with
  | .curve _ => inputKeyLabel curveKey (circuitBucketWire bucket) branch
  | .point _ _ => inputKeyLabel pointKey (circuitBucketWire bucket) branch

/-- The bucket source gives each actual gate label. -/
theorem circuitSourceLabels_gate (curveKey pointKey : InputMacKey)
    (gate : RawCircuitGate) (branch : Bool) :
    circuitSourceLabels curveKey pointKey
      (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) (.hash 0)))
      branch = BitAdaptor.encode (circuitGateKey pointKey curveKey gate) branch := by
  rcases gate with ⟨adaptor, position⟩ | ⟨row, gate⟩
  · fin_cases adaptor <;>
      simp [circuitSourceLabels, circuitBucketWire, circuitGateKey, rawCircuitLocation,
        rawCircuitWindow, rawLabelBucket, fixedKeyIndex, Pipeline.FixedKeyLocation.kind,
        Nat.mod_eq_of_lt position.isLt, inputKeyLabel]
  · rcases gate with ⟨adaptor, position⟩ | (⟨adaptor, position⟩ | ⟨adaptor, position⟩) <;>
      fin_cases adaptor <;>
      simp [circuitSourceLabels, circuitBucketWire, circuitGateKey, rawCircuitLocation,
        rawCircuitWindow, rawLabelBucket, fixedKeyIndex, Pipeline.FixedKeyLocation.kind,
        Nat.mod_eq_of_lt position.isLt, inputKeyLabel]

/-- The label replacement recovers the actual source prescription. -/
theorem rawGatesWithLabels_circuitSourceLabels (curveKey pointKey : InputMacKey)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table) :
    rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
      (circuitSourceLabels curveKey pointKey) =
      circuitRawGatePrescription (circuitGateKey pointKey curveKey) slopes lifts tables := by
  funext gate
  simp only [rawGatesWithLabels, circuitRawGatePrescription]
  rw [circuitSourceLabels_gate, circuitSourceLabels_gate]
  rfl

/-- Each invalid hidden label has one source tape index. -/
def independentBucketWire (bucket : RawLabelBucket) (branch : Bool) : IndependentLabelWire :=
  match bucket.1 with
  | .curve _ => .inl (circuitBucketWire bucket)
  | .point _ _ => .inr (circuitBucketWire bucket, branch)

/-- The independent key split gives the exact mixed-label source. -/
theorem independentKeyLabels_source (selected : EncPRF.PermutationIndex → Bool)
    (keys : InputMacKey × InputMacKey) :
    partialRawLabels (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
      (fun bucket _ => (independentKeyLabelsEquiv selected keys).1 (circuitBucketWire bucket))
      independentBucketWire (fun _ _ => 0) (independentKeyLabelsEquiv selected keys).2 =
      circuitSourceLabels keys.1 keys.2 := by
  funext bucket branch
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor =>
      change (if decide (branch = selected (circuitBucketWire _)) then
        inputKeyLabel keys.1 _ (selected (circuitBucketWire _)) else
        inputKeyLabel keys.1 _ (!(selected (circuitBucketWire _))) ^^^ 0) = _
      cases selected (circuitBucketWire (.curve adaptor, position)) <;> cases branch <;> simp [circuitSourceLabels]
  | point coordinate adaptor =>
      simp [partialRawLabels, curveOnlyExposed, independentBucketWire,
        independentKeyLabelsEquiv, circuitSourceLabels]


/-- Each linked point bucket uses its actual fixed EncPRF pad. -/
def circuitBucketPad (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (bucket : RawLabelBucket) (branch : Bool) : Block :=
  match bucket.1 with
  | .curve _ => 0
  | .point _ _ => evenMansour (oracle.encOracle.permutation (circuitBucketWire bucket))
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) branch

/-- The valid source keeps the original hash and EncPRF link. -/
theorem circuitSourceLabels_linked (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (key : InputMacKey) (bucket : RawLabelBucket) (branch : Bool) :
    circuitSourceLabels key (EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) bucket branch =
      inputKeyLabel key (circuitBucketWire bucket) branch ^^^
        circuitBucketPad oracle bridgeKey bucket branch := by
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor => simp [circuitSourceLabels, circuitBucketPad]
  | point coordinate adaptor => exact linkedLabel_fixedShift oracle bridgeKey key _ branch

/-- The selected-key split gives the exact linked-label source. -/
theorem selectedKeyLabels_source (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (selected : EncPRF.PermutationIndex → Bool) (key : InputMacKey) :
    partialRawLabels (fun bucket branch => decide (branch = selected (circuitBucketWire bucket)))
      (fun bucket branch => (selectedKeyLabelsEquiv selected key).1 (circuitBucketWire bucket) ^^^
        circuitBucketPad oracle bridgeKey bucket branch)
      (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey)
      (selectedKeyLabelsEquiv selected key).2 =
      circuitSourceLabels key (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key) := by
  funext bucket branch
  rw [circuitSourceLabels_linked]
  change (if decide (branch = selected (circuitBucketWire bucket)) then
    inputKeyLabel key _ (selected (circuitBucketWire bucket)) ^^^ _ else
    inputKeyLabel key _ (!(selected (circuitBucketWire bucket))) ^^^ _) = _
  cases selected (circuitBucketWire bucket) <;> cases branch <;> rfl

local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The independent source averages exactly over public labels and hidden labels. -/
theorem independentSourceLabels_uniform [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool) :
    (PMF.uniformOfFintype (InputMacKey × InputMacKey)).map
      (fun keys => ((independentKeyLabelsEquiv selected keys).1, circuitSourceLabels keys.1 keys.2)) =
    (PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (IndependentLabelWire → Block))).map
      (fun sample => (sample.1, partialRawLabels
        (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
        (fun bucket _ => sample.1 (circuitBucketWire bucket))
        independentBucketWire (fun _ _ => 0) sample.2)) := by
  rw [← map_uniform_independentKeyLabels selected, PMF.map_comp]
  congr 1
  funext keys
  exact congrArg (fun labels => (_, labels)) (independentKeyLabels_source selected keys).symm

/-- The valid source averages exactly over selected labels and unused labels. -/
theorem linkedSourceLabels_uniform [Fintype Block]
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (selected : EncPRF.PermutationIndex → Bool) :
    (PMF.uniformOfFintype InputMacKey).map
      (fun key => ((selectedKeyLabelsEquiv selected key).1, circuitSourceLabels key (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key))) =
    (PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))).map
      (fun sample => (sample.1, partialRawLabels
        (fun bucket branch => decide (branch = selected (circuitBucketWire bucket)))
        (fun bucket branch => sample.1 (circuitBucketWire bucket) ^^^
          circuitBucketPad oracle bridgeKey bucket branch)
        (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey) sample.2)) := by
  rw [← map_uniform_selectedKeyLabels selected, PMF.map_comp]
  congr 1
  funext key
  exact congrArg (fun labels => (_, labels)) (selectedKeyLabels_source oracle bridgeKey selected key).symm


/-- The actual input fixes one selected label at each coordinate index. -/
def inputSelectedLabelBit (input : AffineInput) (index : EncPRF.PermutationIndex) : Bool :=
  match index.1 with
  | .x => coordinateValues input.x index.2
  | .y => coordinateValues input.y index.2

/-- The circuit and coordinate selectors use the same input bit. -/
theorem circuitBucketInputBit_wire (input : AffineInput) (bucket : RawLabelBucket) :
    circuitBucketInputBit input bucket = inputSelectedLabelBit input (circuitBucketWire bucket) := by
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor => cases adaptor <;> rfl
  | point coordinate adaptor => cases coordinate <;> cases adaptor <;> rfl

set_option maxRecDepth 4096 in
/-- The selected source labels equal the labels that the adversary receives. -/
theorem circuitSourceLabels_selected (curveKey pointKey : InputMacKey)
    (input : AffineInput) (bucket : RawLabelBucket) :
    circuitSourceLabels curveKey pointKey bucket (circuitBucketInputBit input bucket) =
      circuitBucketInputLabel (curveKey.encodeAffine input) (pointKey.encodeAffine input) bucket := by
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor => cases adaptor <;>
      simp [circuitSourceLabels, circuitBucketWire, circuitBucketInputBit, circuitBucketInputLabel,
        InputMacKey.encodeAffine, InputMacKey.encode, encodeCoordinate, BitInput.ofAffine,
        inputKeyLabel, coordinateValues, Vector.get_eq_getElem]
  | point coordinate adaptor => cases coordinate <;> cases adaptor <;>
      simp [circuitSourceLabels, circuitBucketWire, circuitBucketInputBit, circuitBucketInputLabel,
        InputMacKey.encodeAffine, InputMacKey.encode, encodeCoordinate, BitInput.ofAffine,
        inputKeyLabel, coordinateValues, Vector.get_eq_getElem]


/-- Each independent hidden tape reconstructs the exact actual gate family. -/
theorem independentSource_gates (selected : EncPRF.PermutationIndex → Bool)
    (sample : (EncPRF.PermutationIndex → Block) × (IndependentLabelWire → Block))
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table) :
    rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
      (partialRawLabels (curveOnlyExposed (fun bucket => selected (circuitBucketWire bucket)))
        (fun bucket _ => sample.1 (circuitBucketWire bucket))
        independentBucketWire (fun _ _ => 0) sample.2) =
    circuitRawGatePrescription
      (circuitGateKey ((independentKeyLabelsEquiv selected).symm sample).2
        ((independentKeyLabelsEquiv selected).symm sample).1) slopes lifts tables := by
  have labels := independentKeyLabels_source selected ((independentKeyLabelsEquiv selected).symm sample)
  rw [Equiv.apply_symm_apply] at labels
  rw [labels, rawGatesWithLabels_circuitSourceLabels]

/-- Each linked hidden tape reconstructs the exact actual gate family. -/
theorem linkedSource_gates (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (selected : EncPRF.PermutationIndex → Bool)
    (sample : (EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block))
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table) :
    rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
      (partialRawLabels (fun bucket branch => decide (branch = selected (circuitBucketWire bucket)))
        (fun bucket branch => sample.1 (circuitBucketWire bucket) ^^^
          circuitBucketPad oracle bridgeKey bucket branch)
        (fun bucket _ => circuitBucketWire bucket) (circuitBucketPad oracle bridgeKey) sample.2) =
    circuitRawGatePrescription
      (circuitGateKey (EncPRF.transformKey oracle.encOracle
        (EncPRF.whiteningKeys oracle.hashOracle bridgeKey)
          ((selectedKeyLabelsEquiv selected).symm sample))
        ((selectedKeyLabelsEquiv selected).symm sample)) slopes lifts tables := by
  have labels := selectedKeyLabels_source oracle bridgeKey selected
    ((selectedKeyLabelsEquiv selected).symm sample)
  rw [Equiv.apply_symm_apply] at labels
  rw [labels, rawGatesWithLabels_circuitSourceLabels]

end
end Kriterion.ArgoMAC.Security
