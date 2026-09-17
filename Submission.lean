import Solution
import Construction
import Proof

-- The packed encoding is a 8,065-byte-per-adaptor structure. Unfolding it
-- during elaboration is expensive and never needed: the length theorems are
-- proved where the encoding is defined.
attribute [local irreducible] Kriterion.ArgoMAC.Wire.encoding

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

-- The packed adaptor encoding is 8,065 bytes, so checking one length walks
-- that many constructors.
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The wire adapter preserves the complete ciphertext and removes repeated input bits. -/
def solution : Kriterion.Solution := {
  FixedIndex := Pipeline.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Seed.randomness 0
  Public := Pipeline.PackedTable
  EncodingKey := Garbling.EncodingKey
  State := Security.CircuitSimulatorState
  encoding := Wire.encoding
  ciphertextBytes := 8891172
  evaluationOracle := fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
  oracleUniform := by
    convert Security.oracleUniform (Seed.randomness 0) using 1
  scheme := fun field group => @Lamport.packedCircuit field group
  ciphertextSize := by
    intro field group parameter scalar tape
    letI := field
    letI := group
    exact Wire.ciphertextSize parameter scalar tape
  lamportCompatible := fun field group => @Lamport.packedCompatible field group
  idealOracle := Security.circuitSimulatorOracleHandler
  idealView := Security.CircuitSimulatorState.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @packedPerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    let pack := fun labels : Garbling.Labels => Lamport.selectedLabels labels.inputMac
    let restore := fun _ : Nat => (⟨508, 91⟩ : Garbling.Topology)
    refine ⟨(Security.concreteCircuitSimulator.mapLabels pack restore).mapPublic
        Pipeline.Table.pack,
      (Security.concreteCircuitSimulator_rules.mapLabels pack restore).mapPublic
        Pipeline.Table.pack, ?_⟩
    have privacy := ((Security.concreteAdaptivePrivacy (Aux := Unit) (Seed.randomness 0)).mapLabels
      pack Lamport.restore (fun _ => 8891172) restore (fun _ => rfl)).mapPublic
      Pipeline.Table.pack Pipeline.PackedTable.unpack
    have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
        Security.garblingRandomnessFintype := Subsingleton.elim _ _
    have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
        (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
      unfold uniformRandomTape Security.randomTape
      rw [Cryptography.uniformTape_eq, instances]
    rw [tapes]
    exact privacy
}

end Submission
