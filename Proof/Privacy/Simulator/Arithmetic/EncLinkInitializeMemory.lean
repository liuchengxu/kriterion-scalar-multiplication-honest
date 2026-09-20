import Proof.Privacy.Simulator.Arithmetic.EncLinkInitialize
import Proof.Privacy.Simulator.Arithmetic.EncLinkInvariant
import Proof.Privacy.Simulator.Arithmetic.EncLinkFrame
import Proof.Privacy.Simulator.Arithmetic.OracleFamilySource
import Proof.Privacy.Simulator.Arithmetic.HashPrivate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block preserves every physical public oracle cell. -/
theorem encLinkSaved_public (memory : Memory) (oracle : Fin 15749) (region : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    (encLinkSaved memory).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  have small (cell : Nat) (bound : cell < 256) :
      oracleAddress oracle region offset ≠ BitVec.ofNat 256 cell :=
    oracleAddress_private_disjoint oracle region offset cell fits (by omega)
  simp [encLinkSaved, encLinkSave, executeLinear, LinearInstruction.execute,
    small 32 (by decide), small 33 (by decide), small 34 (by decide),
    small 35 (by decide), small 36 (by decide), small 38 (by decide)]

/-- The save block preserves the complete finite oracle family. -/
theorem encLinkSaved_family (memory : Memory) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state) :
    OracleFamilyMemory (encLinkSaved memory).ram state :=
  OracleFamilyMemory.congr _ _ state represented capacity (encLinkSaved_public memory)

/-- The schedule writes only its two private key cells. -/
theorem encLinkScheduled_public (memory : Memory) (oracle : Fin 15749) (region : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    (encLinkScheduled memory).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [(encLinkScheduled_memory memory).1,
    privateUpdate_public _ 40 _ (by decide) _ _ _ fits,
    privateUpdate_public _ 39 _ (by decide) _ _ _ fits]

/-- The schedule preserves the complete finite oracle family. -/
theorem encLinkScheduled_family (memory : Memory) (state : SparseOracleFamily)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state) :
    OracleFamilyMemory (encLinkScheduled memory).ram state :=
  OracleFamilyMemory.congr _ _ state represented capacity (encLinkScheduled_public memory)

/-- Every initialized hash sample satisfies the complete 508-row loop invariant. -/
theorem encLinkInitialize_ready (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (key : BN254.BaseField) (output limit : Nat) (suffix : List Bool)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : memory.registers 8 = hashKeyWord key)
    (outputBase : memory.registers 14 = BitVec.ofNat 256 output)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (baseCount : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlayCount : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110)
    (wire : memory.bits 0 = suffix)
    (supported : (final, cost) ∈ (hashHandlerSamples state.hash.length (encLinkSaved memory)).support) :
    EncLinkLoopMemory (state.updateHash (hashNextTable state.hash key (final.registers 8).toFin))
      (encLinkScheduled final) encLinkIndices suffix
      (Security.SimulatorMachine.hashFin.symm (final.registers 8).toFin).1 output limit := by
  have saved := encLinkSave_state memory
  have savedFamily := encLinkSaved_family memory state represented capacity
  have index : (encLinkSaved memory).registers 9 = BitVec.ofNat 256 15748 := saved.2.1
  have savedOperand : (encLinkSaved memory).registers 8 = hashKeyWord key := saved.1.trans operand
  have counter : (encLinkSaved memory).ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.hash.length := by
    simpa only [hashWordPairs, List.length_map] using savedFamily.hash.count
  have family := hashHandlerSamples_family (encLinkSaved memory) final cost state key
    savedFamily capacity index savedOperand hashRoom supported
  rw [publicHashTail_ram] at family
  have nextCapacity : OracleFamilyFits (state.updateHash (hashNextTable state.hash key (final.registers 8).toFin)) := by
    refine ⟨capacity.base, capacity.overlay, ?_⟩
    change 2 * (hashNextTable state.hash key (final.registers 8).toFin).length ≤ 2 ^ 110
    unfold hashNextTable
    split <;> (try simp only [List.length_cons]) <;> omega
  have kept (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
      final.ram (BitVec.ofNat 256 cell) = (encLinkSaved memory).ram (BitVec.ofNat 256 cell) :=
    hashHandlerSamples_private state.hash.length (encLinkSaved memory) final cost supported
      15748 index counter (by omega) cell lower upper
  have length : encLinkIndices.length = 508 := by
    simp [encLinkIndices, coordinateBitCount]
  refine ⟨encLinkScheduled_family final _ family nextCapacity, nextCapacity, baseCount, overlayCount,
    ?_, ?_, ?_, outputLower, ?_, (encLinkScheduled_keys final).1, ?_⟩
  · simpa only [length] using room
  · rw [(encLinkScheduled_memory final).1]
    simp only [Function.update_of_ne (by decide : (38 : Word) ≠ 40),
      Function.update_of_ne (by decide : (38 : Word) ≠ 39), length]
    exact (kept 38 (by decide) (by decide)).trans saved.2.2.2.2.2.2.2.2.1
  · rw [(encLinkScheduled_memory final).1]
    simp only [Function.update_of_ne (by decide : (33 : Word) ≠ 40),
      Function.update_of_ne (by decide : (33 : Word) ≠ 39)]
    exact (kept 33 (by decide) (by decide)).trans (saved.2.2.2.2.1.trans outputBase)
  · simpa only [length] using outputUpper
  · rw [(encLinkScheduled_memory final).2, Function.update_self,
      hashHandlerSamples_bits state.hash.length (encLinkSaved memory) final cost supported]
    change encLinkIndexWire ++ memory.bits 0 = _
    rw [wire]
    rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
