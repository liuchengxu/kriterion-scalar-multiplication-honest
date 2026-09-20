import Proof.Privacy.Simulator.Arithmetic.GateDriverJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- The branch arithmetic preserves the complete RAM function. -/
theorem gateBlocksMemory_ram (tweak : Block) (bit : Bool) (memory : Memory) :
    (gateBlocksMemory tweak bit memory).ram = memory.ram := by
  unfold gateBlocksMemory
  cases bit
  · exact (gateHashProgram_preserves memory tweak).1
  · exact (gatePadProgram_preserves memory tweak).1

/-- Gate preparation changes only its ten saved scratch words. -/
theorem gateDriverPrepared_outside (gate : GateCode) (memory : Memory) (address : Word)
    (outside : address ≠ 16 ∧ address ≠ 17 ∧ address ≠ 18 ∧ address ≠ 19 ∧ address ≠ 20 ∧
      address ≠ 21 ∧ address ≠ 22 ∧ address ≠ 23 ∧ address ≠ 24 ∧ address ≠ 25) :
    (gateDriverPrepared gate memory).ram address = memory.ram address := by
  unfold gateDriverPrepared
  rw [gateDirectiveSave_outside _ address outside, gateBlocksMemory_ram,
    (gateDirectiveLoad_preserves gate.selected gate.target gate.quotient gate.table memory).1]

/-- Gate preparation preserves every public oracle cell. -/
theorem gateDriverPrepared_public (gate : GateCode) (memory : Memory) (oracle : Fin 15749)
    (region : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (gateDriverPrepared gate memory).ram (oracleAddress oracle region offset) = memory.ram (oracleAddress oracle region offset) := by
  apply gateDriverPrepared_outside
  exact ⟨oracleAddress_private_disjoint oracle region offset 16 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 17 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 18 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 19 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 20 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 21 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 22 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 23 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 24 fits (by decide),
    oracleAddress_private_disjoint oracle region offset 25 fits (by decide)⟩

/-- Gate preparation preserves every private caller buffer above the scratch words. -/
theorem gateDriverPrepared_private (gate : GateCode) (memory : Memory) (cell : Nat)
    (lower : 32 ≤ cell) (privateBound : cell < 2 ^ 96) :
    (gateDriverPrepared gate memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  apply gateDriverPrepared_outside
  exact ⟨privateWord_ne cell 16 privateBound (by decide) (by omega),
    privateWord_ne cell 17 privateBound (by decide) (by omega),
    privateWord_ne cell 18 privateBound (by decide) (by omega),
    privateWord_ne cell 19 privateBound (by decide) (by omega),
    privateWord_ne cell 20 privateBound (by decide) (by omega),
    privateWord_ne cell 21 privateBound (by decide) (by omega),
    privateWord_ne cell 22 privateBound (by decide) (by omega),
    privateWord_ne cell 23 privateBound (by decide) (by omega),
    privateWord_ne cell 24 privateBound (by decide) (by omega),
    privateWord_ne cell 25 privateBound (by decide) (by omega)⟩

/-- Gate preparation preserves the represented source and all count caps. -/
theorem SharedSourceMemory.gatePrepared (gate : GateCode) {memory : Memory} {state : SharedOracleSource} {limit : Nat}
    (represented : SharedSourceMemory memory state limit) (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    SharedSourceMemory (gateDriverPrepared gate memory) state limit := by
  refine ⟨OracleFamilyMemory.congr memory.ram _ state.family represented.family represented.capacity
    (gateDriverPrepared_public gate memory), represented.capacity, ?_, represented.counts⟩
  intro index
  exact HistoryMemory.congr memory.ram _ _ _ (represented.history index) (represented.historyFits room index)
    (gateDriverPrepared_public gate memory _ 3)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
