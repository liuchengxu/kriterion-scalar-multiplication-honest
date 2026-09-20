import Proof.Privacy.Simulator.Arithmetic.GateDriverHostCode
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveLoad
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveScratch
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The gate source reads the selected coordinate bit. -/
def gateDriverBit (gate : GateCode) (memory : Memory) : Bool :=
  (memory.ram (memory.registers 12 + BitVec.ofNat 256 (selectedCoordinate gate.selected))).getLsbD
    (selectedBit gate.selected)

/-- The prefix saves the exact selected input and two or three output ranges. -/
def gateDriverPrepared (gate : GateCode) (memory : Memory) : Memory :=
  executeLinear gateDirectiveSave (gateBlocksMemory gate.tweak (gateDriverBit gate memory)
    (executeLinear (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) memory))

def gateDriverPrefixCost (gate : GateCode) (memory : Memory) : Nat :=
  21 + gateBlocksCost (gateDriverBit gate memory) + 20

/-- The prefix charges at most sixty-nine fixed instructions. -/
theorem gateDriverPrefixCost_bound (gate : GateCode) (memory : Memory) :
    gateDriverPrefixCost gate memory ≤ 69 := by
  unfold gateDriverPrefixCost gateBlocksCost
  split <;> omega

/-- The host prefix returns the prepared gate memory with its exact charge. -/
theorem gateDriverBlock_prefix [BN254.FieldCertificate] (host : Machine) (attempts : Nat) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsGateDriver host attempts gate labels)
    (memory : Memory) (fuel : Nat) :
    run host (gateDriverPrefixCost gate memory + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 80, gateDriverPrepared gate memory⟩).map
        (Option.map fun result => (result.1, result.2 + gateDriverPrefixCost gate memory)) := by
  let loaded := executeLinear (gateDirectiveLoad gate.selected gate.target gate.quotient gate.table) memory
  have encoded : loaded.registers 10 = if gateDriverBit gate memory then 1 else 0 := by
    rw [(gateDirectiveLoad_values gate.selected gate.target gate.quotient gate.table memory).2.2.2.2]
    exact selected_bit_mask _ _
  have load := gateDirectiveLoadHost_continue host gate.selected gate.target gate.quotient gate.table
    (labels ∘ gateDriverLoadLabels) (gateDriverBlock_load host attempts gate labels present) memory
    (20 + fuel + gateBlocksCost (gateDriverBit gate memory))
  change run host (21 + (20 + fuel + gateBlocksCost (gateDriverBit gate memory))) ⟨labels 0, memory⟩ =
    (run host (20 + fuel + gateBlocksCost (gateDriverBit gate memory)) ⟨labels 21, loaded⟩).map _ at load
  have blocks := gateBlocksHost_continue host gate.tweak (labels ∘ gateDriverBlocksLabels)
    (gateDriverBlock_blocks host attempts gate labels present) loaded (gateDriverBit gate memory) encoded (20 + fuel)
  change run host (20 + fuel + gateBlocksCost (gateDriverBit gate memory)) ⟨labels 21, loaded⟩ =
    (run host (20 + fuel) ⟨labels 60, gateBlocksMemory gate.tweak (gateDriverBit gate memory) loaded⟩).map _ at blocks
  have save := linear_continue host gateDirectiveSave (labels ∘ gateDriverSaveLabels)
    (gateDriverBlock_save host attempts gate labels present)
    (gateBlocksMemory gate.tweak (gateDriverBit gate memory) loaded) fuel
  change run host (20 + fuel) ⟨labels 60, gateBlocksMemory gate.tweak (gateDriverBit gate memory) loaded⟩ =
    (run host fuel ⟨labels 80, gateDriverPrepared gate memory⟩).map _ at save
  rw [show gateDriverPrefixCost gate memory + fuel = 21 + (20 + fuel + gateBlocksCost (gateDriverBit gate memory)) by unfold gateDriverPrefixCost; omega]
  rw [load, blocks, save]
  simp only [show gateDirectiveSave.length = 20 from rfl]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, gateDriverPrefixCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
