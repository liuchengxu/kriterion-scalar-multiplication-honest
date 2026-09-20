import Proof.Privacy.Simulator.Arithmetic.OnlineCurveTyped
import Proof.Privacy.Simulator.Arithmetic.SharedHistoryRecord

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SharedSimulatorMachine

/-- The input record occupies only private RAM. -/
theorem onlineReadMemory_public [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (oracle : Fin 15749) (region : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    (onlineReadMemory memory input output rest).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [onlineReadMemory, (onlineInputMemory_values (onlineInputPrepared memory) input output rest).1]
  have pointer : (onlineInputPrepared memory).registers 10 = BitVec.ofNat 256 onlineInputBase := rfl
  have apart (cell : Fin 5) : oracleAddress oracle region offset ≠
      BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 cell.val := by
    rw [← BitVec.ofNat_add]
    apply oracleAddress_private_disjoint oracle region offset _ fits
    have small := cell.isLt
    have fixed : onlineInputBase + 5 < 2 ^ 96 := by decide
    omega
  simp only [onlineRecordRam, pointer]
  rw [Function.update_of_ne (show oracleAddress oracle region offset ≠ BitVec.ofNat 256 onlineInputBase + (4 : Word) from apart 4),
    Function.update_of_ne (show oracleAddress oracle region offset ≠ BitVec.ofNat 256 onlineInputBase + (3 : Word) from apart 3),
    Function.update_of_ne (show oracleAddress oracle region offset ≠ BitVec.ofNat 256 onlineInputBase + (2 : Word) from apart 2),
    Function.update_of_ne (show oracleAddress oracle region offset ≠ BitVec.ofNat 256 onlineInputBase + (1 : Word) from apart 1),
    Function.update_of_ne (by simpa using apart 0)]
  rfl

/-- The original-label store leaves every public oracle cell unchanged. -/
theorem onlineOriginalMemory_public [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (oracle : Fin 15749) (region : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    (onlineOriginalMemory memory input output rest).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  have setup := onlineOriginalSetup_state (onlineReadMemory memory input output rest)
  rw [onlineOriginalMemory, selectedLabelStoreCode_outside]
  · rw [setup.1]
    exact onlineReadMemory_public memory input output rest oracle region offset fits
  · intro index
    rw [setup.2.2.2.2, ← BitVec.ofNat_add]
    apply oracleAddress_private_disjoint oracle region offset _ fits
    have small := index.isLt
    have fixed : onlineOriginalBase + 508 < 2 ^ 96 := by decide
    omega

/-- The complete curve prefix leaves every public oracle cell unchanged. -/
theorem onlineCurveMemory_public [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (oracle : Fin 15749) (region : Fin 4)
    (offset : Nat) (fits : offset < 2 ^ 110) :
    (onlineCurveMemory memory input output rest).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [onlineCurveMemory, retargetCurveCode_outside]
  · exact onlineOriginalMemory_public memory input output rest oracle region offset fits
  · rw [(onlineOriginalMemory_pointers memory input output rest).1]
    change oracleAddress oracle region offset ≠ BitVec.ofNat 256 privateBase + BitVec.ofNat 256 834903
    rw [← BitVec.ofNat_add]
    exact oracleAddress_private_disjoint oracle region offset _ fits (by decide)

/-- The complete curve prefix retains the exact shared source relation. -/
theorem onlineCurveMemory_shared [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (state : SharedOracleSource) (limit : Nat)
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    SharedSourceMemory (onlineCurveMemory memory input output rest) state limit := by
  refine ⟨OracleFamilyMemory.congr _ _ state.family represented.family represented.capacity
    (onlineCurveMemory_public memory input output rest), represented.capacity, ?_, represented.counts⟩
  exact SharedHistoryMemory.fixedFrame _ _ state.metadata state.metadata represented.history rfl
    (represented.historyFits room) (fun index offset fits => onlineCurveMemory_public memory input output rest _ 3 offset fits)

/-- The absent-output curve loop starts with the exact original shared source. -/
theorem onlineNullGateInitial_shared [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (state : SharedOracleSource) (limit : Nat)
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    SharedSourceMemory (onlineNullGateInitial (onlineCurveMemory memory input output rest)) state limit :=
  (onlineCurveMemory_shared memory input output rest state limit represented room).ramEq
    (onlineOriginalSetup_state (onlineTagMemory (onlineCurveMemory memory input output rest))).1

/-- The actual offline array and public source establish the complete curve-loop invariant. -/
theorem onlineNull_ready [FieldCertificate] (attempts limit : Nat)
    (memory : Memory) (input : AffineInput) (output : Option Point) (rest : List Bool)
    (coin : Security.SimulatorSampling.OfflineCoin) (state : SharedOracleSource)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin))
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3810) < 2 ^ 110) :
    GateLoopCoupledReady curveGatePlan
      (fun gate => sharedDirectiveSlot (curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate))
      (fun gate => !(curveDirectiveAt ((sharedOfflineFrame coin).selectedCurve input)
        input ((sharedOfflineFrame coin).labels input).inputMac gate).bit)
      attempts 1270 0 limit (onlineNullGateInitial (onlineCurveMemory memory input output rest)) state :=
  onlineCurveInitial_ready attempts limit memory input output rest coin state stored
    (onlineNullGateInitial_shared memory input output rest state limit represented (by omega)) room

end Kriterion.ArgoMAC.ArithmeticSimulator
