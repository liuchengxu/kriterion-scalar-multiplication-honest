import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerInput
import Proof.Privacy.Simulator.Arithmetic.SharedSourceCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
noncomputable section

/-- The recorded reader retains the query fields and saves only the operand and tag. -/
theorem recordedPublicInputMemory_values (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (recordedPublicInputMemory memory request rest).registers 8 = (queryOperands request).1 ∧
    (recordedPublicInputMemory memory request rest).registers 9 = (queryOperands request).2.1 ∧
    (recordedPublicInputMemory memory request rest).registers 10 = (queryOperands request).2.2 ∧
    (recordedPublicInputMemory memory request rest).bits 0 = rest ∧
    (recordedPublicInputMemory memory request rest).ram =
      Function.update (Function.update memory.ram 48 (queryOperands request).1) 49 (queryOperands request).2.2 := by
  have decoded := queryInputMemory_values memory request rest
  have saved := publicHistorySave_state (queryInputMemory memory request rest)
  have dispatched := publicDispatchMemory_data (executeLinear publicHistorySave (queryInputMemory memory request rest))
  refine ⟨dispatched.1.trans (saved.2.2.1.trans decoded.1),
    dispatched.2.1.trans (saved.2.2.2.1.trans decoded.2.1),
    dispatched.2.2.1.trans (saved.2.2.2.2.trans decoded.2.2.1), ?_, ?_⟩
  · exact (congrFun dispatched.2.2.2.2 0).trans ((congrFun saved.2.1 0).trans decoded.2.2.2.1)
  · exact dispatched.2.2.2.1.trans (saved.1.trans (by rw [decoded.2.2.2.2, decoded.1, decoded.2.2.1]))

/-- The recorded reader preserves every public oracle cell, including all history regions. -/
theorem recordedPublicInputMemory_public (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (recordedPublicInputMemory memory request rest).ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  rw [(recordedPublicInputMemory_values memory request rest).2.2.2.2]
  have separate49 : oracleAddress oracle table offset ≠ (49 : Word) :=
    oracleAddress_private_disjoint oracle table offset 49 fits (by decide)
  have separate48 : oracleAddress oracle table offset ≠ (48 : Word) :=
    oracleAddress_private_disjoint oracle table offset 48 fits (by decide)
  simp only [Function.update_of_ne separate49, Function.update_of_ne separate48]

/-- The actual recorded reader retains the complete finite oracle family. -/
theorem recordedPublicInputMemory_family (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (state : SparseOracleFamily) (represented : OracleFamilyMemory memory.ram state) (fits : OracleFamilyFits state) :
    OracleFamilyMemory (recordedPublicInputMemory memory request rest).ram state :=
  OracleFamilyMemory.congr memory.ram _ state represented fits
    (recordedPublicInputMemory_public memory request rest)

/-- The recorded reader saves the exact request needed by the public history appender. -/
theorem recordedPublicInputMemory_saved (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (recordedPublicInputMemory memory request rest).ram 48 = (queryOperands request).1 ∧
    (recordedPublicInputMemory memory request rest).ram 49 = (queryOperands request).2.2 := by
  rw [(recordedPublicInputMemory_values memory request rest).2.2.2.2]
  simp

end
end Kriterion.ArgoMAC.ArithmeticSimulator
