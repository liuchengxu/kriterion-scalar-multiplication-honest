import Proof.Privacy.Simulator.Arithmetic.OfflineWireSource
import Construction.Simulator.MemoryLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] publicWireProgram offlinePlan

/-- The offline table contains two address loads, the sampler, and the serializer. -/
noncomputable def offlineMachineSize : Nat := 2 + 39 * 838208 + publicWireProgram.length

theorem offlineMachineSize_fits : offlineMachineSize < 2 ^ 256 := by
  have bound := publicWireMachine_budget
  change publicWireProgram.length + 1 + (publicWireProgram.length + 1) ≤ 477065504 at bound
  unfold offlineMachineSize
  omega

/-- The batch return continues at the first serializer instruction. -/
noncomputable def offlineBatchLabel (pc : Fin (39 * 838208 + 1)) : Fin (offlineMachineSize + 1) :=
  ⟨2 + pc.val, by have bound := pc.isLt; unfold offlineMachineSize; omega⟩

/-- The serializer return points to the final halt. -/
noncomputable def offlineWireLabel (index : Nat) : Fin (offlineMachineSize + 1) :=
  ⟨2 + 39 * 838208 + min index publicWireProgram.length, by unfold offlineMachineSize; omega⟩

/-- The checked package keeps the fixed sampler table symbolic. -/
private noncomputable def offlineBatchCodePackage (attempts : Nat) :
    {code : Vector (Instruction (39 * 838208 + 1)) (39 * 838208 + 1) //
      code = (samplerBatch offlinePlan attempts (by decide)).code} :=
  Classical.choice ⟨⟨(samplerBatch offlinePlan attempts (by decide)).code, rfl⟩⟩

noncomputable def offlineBatchCode (attempts : Nat) : Vector (Instruction (39 * 838208 + 1)) (39 * 838208 + 1) :=
  (offlineBatchCodePackage attempts).val

theorem offlineBatchCode_eq (attempts : Nat) :
    offlineBatchCode attempts = (samplerBatch offlinePlan attempts (by decide)).code :=
  (offlineBatchCodePackage attempts).property

/-- The complete offline machine uses only fixed arithmetic instructions. -/
noncomputable def offlineMachine (attempts : Nat) : Machine := ⟨offlineMachineSize,
  Vector.ofFn (fun pc =>
    if pc.val = 0 then .constant 10 (BitVec.ofNat 256 privateBase) ⟨1, by unfold offlineMachineSize; omega⟩
    else if pc.val = 1 then .constant 11 (BitVec.ofNat 256 privateBase) (offlineBatchLabel 0)
    else if batch : pc.val < 2 + 39 * 838208 then
      relocate offlineBatchLabel ((offlineBatchCode attempts)[pc.val - 2]'(by omega))
    else if wire : pc.val < offlineMachineSize then
      (publicWireProgram[pc.val - (2 + 39 * 838208)]'(by unfold offlineMachineSize at wire; omega)).emit
        ⟨pc.val + 1, by omega⟩
    else .halt), offlineMachineSize_fits⟩

/-- The first instruction selects the sampler address. -/
theorem offlineMachine_zero (attempts : Nat) :
    (offlineMachine attempts).code[0] = .constant 10 (BitVec.ofNat 256 privateBase)
      ⟨1, by change 1 < offlineMachineSize + 1; unfold offlineMachineSize; omega⟩ := by
  simp [offlineMachine]

/-- The second instruction selects the serializer address. -/
theorem offlineMachine_one (attempts : Nat) :
    (offlineMachine attempts).code[1]'(by change 1 < offlineMachineSize + 1; unfold offlineMachineSize; omega) =
      .constant 11 (BitVec.ofNat 256 privateBase) (offlineBatchLabel 0) := by
  simp [offlineMachine]

/-- The complete table contains every sampler instruction. -/
theorem offlineMachine_batch (attempts : Nat) :
    ContainsSamplerBatch (offlineMachine attempts) offlinePlan attempts (by decide) offlineBatchLabel := by
  intro pc inside
  have lower : 2 + pc.val ≠ 0 := by omega
  have next : 2 + pc.val ≠ 1 := by omega
  have upper : 2 + pc.val < 2 + 39 * 838208 := by omega
  simp only [offlineMachine, Vector.getElem_ofFn, offlineBatchLabel, lower, next, if_false,
    upper, dite_true, Nat.add_sub_cancel_left]
  exact congrArg (fun code : Vector (Instruction (39 * 838208 + 1)) (39 * 838208 + 1) =>
    relocate offlineBatchLabel code[pc.val]) (offlineBatchCode_eq attempts)

/-- The complete table contains every serializer instruction. -/
theorem offlineMachine_wire (attempts : Nat) :
    ContainsLinear (offlineMachine attempts) publicWireProgram offlineWireLabel := by
  intro index valid
  have next : index + 1 ≤ publicWireProgram.length := by omega
  have minimum : min index publicWireProgram.length = index := Nat.min_eq_left (by omega)
  simp only [offlineMachine, Vector.getElem_ofFn, offlineWireLabel, minimum]
  have lower : 2 + 39 * 838208 + index ≠ 0 := by omega
  have second : 2 + 39 * 838208 + index ≠ 1 := by omega
  have batch : ¬ 2 + 39 * 838208 + index < 2 + 39 * 838208 := by omega
  have wire : 2 + 39 * 838208 + index < offlineMachineSize := by unfold offlineMachineSize; omega
  simp only [lower, second, if_false, batch, dite_false, wire, dite_true,
    Nat.add_sub_cancel_left, Nat.min_eq_left next]
  congr 1

/-- The last table entry halts for every positive remaining fuel amount. -/
theorem offlineMachine_halt [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (offlineMachine attempts) (fuel + 1) ⟨offlineWireLabel publicWireProgram.length, memory⟩ =
      PMF.pure (some (⟨offlineWireLabel publicWireProgram.length, memory⟩, 1)) := by
  have different : 2 + 39 * 838208 + publicWireProgram.length ≠ 1 := by omega
  simp [run, step, offlineMachine, offlineWireLabel, offlineMachineSize, different]

end Kriterion.ArgoMAC.ArithmeticSimulator
