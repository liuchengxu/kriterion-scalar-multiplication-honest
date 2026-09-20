import Proof.Privacy.Simulator.Arithmetic.EncLinkRead
import Proof.Privacy.Simulator.Arithmetic.EncLinkTail
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A private RAM write preserves every public oracle cell. -/
theorem privateUpdate_public (ram : Word → Word) (cell value : Word)
    (privateCell : cell.toNat < 2 ^ 96) (oracle : Fin 15749) (table : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    Function.update ram cell value (oracleAddress oracle table offset) =
      ram (oracleAddress oracle table offset) := by
  apply Function.update_of_ne
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
    oracleAddress_private_disjoint oracle table offset cell.toNat fits privateCell

/-- The preparation block preserves every public oracle cell. -/
theorem encLinkPrepared_public (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (oracle : Fin 15749) (table : Fin 4) (offset : Nat)
    (fits : offset < 2 ^ 110) :
    (encLinkPrepared memory index rest).ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  rw [(encLinkPrepared_values memory index rest).2.2.2.1]
  rw [privateUpdate_public _ 35 _ (by decide) _ _ _ fits,
    privateUpdate_public _ 41 _ (by decide) _ _ _ fits]

/-- The controller preserves every public oracle cell. -/
theorem encLinkControlState_public (memory : Memory) (oracle : Fin 15749)
    (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (encLinkControlState memory).1.ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  unfold encLinkControlState
  split
  · exact congrFun (encLinkReturn_state memory).2.1 _
  · split
    · rw [(encLinkSwitch_state (encLinkCompared memory)).1,
        privateUpdate_public _ 35 _ (by decide) _ _ _ fits]
      rfl
    · rfl

/-- The accepted output write preserves every public oracle cell. -/
theorem encLinkAfterQuery_public (memory : Memory)
    (privateOutput : (memory.ram 33).toNat < 2 ^ 96)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (encLinkAfterQuery memory).1.ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  unfold encLinkAfterQuery
  split
  · rfl
  · rw [encLinkControlState_public _ _ _ _ fits,
      encLinkFinish_ram memory inputSafe countSafe]
    rw [privateUpdate_public _ 38 _ (by decide) _ _ _ fits,
      privateUpdate_public _ 32 _ (by decide) _ _ _ fits,
      privateUpdate_public _ 33 _ (by decide) _ _ _ fits,
      privateUpdate_public _ (memory.ram 33) _ privateOutput _ _ _ fits]

/-- The preparation block retains the complete source family. -/
theorem encLinkPrepared_family (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state) :
    OracleFamilyMemory (encLinkPrepared memory index rest).ram state :=
  OracleFamilyMemory.congr _ _ state represented capacity
    (encLinkPrepared_public memory index rest)

/-- The output and control blocks retain the complete source family. -/
theorem encLinkAfterQuery_family (memory : Memory) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (privateOutput : (memory.ram 33).toNat < 2 ^ 96)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    OracleFamilyMemory (encLinkAfterQuery memory).1.ram state :=
  OracleFamilyMemory.congr _ _ state represented capacity
    (encLinkAfterQuery_public memory privateOutput inputSafe countSafe)

end Kriterion.ArgoMAC.ArithmeticSimulator
