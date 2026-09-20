import Proof.Privacy.Simulator.Arithmetic.FixedContinuation
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLinear
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents
import Proof.Privacy.Simulator.Arithmetic.OnlineInputReturn

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The input setup installs the fixed five-word record pointer. -/
def onlineInputPrepared (memory : Memory) : Memory := executeLinear onlineInputSetup memory

/-- The input reader stores the selected input and optional output. -/
def onlineReadMemory [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput) (output : Option BN254.Point)
    (rest : List Bool) : Memory := onlineInputMemory (onlineInputPrepared memory) input output rest

/-- The original-label store keeps the selected labels in their fixed private buffer. -/
noncomputable def onlineOriginalMemory [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) : Memory :=
  executeLinear selectedLabelStoreCode
    (executeLinear onlineOriginalSetup (onlineReadMemory memory input output rest))

/-- The common curve prefix retargets the request before the validity branch. -/
noncomputable def onlineCurveMemory [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) : Memory :=
  executeLinear retargetCurveCode (onlineOriginalMemory memory input output rest)

/-- The common prefix charges input, original labels, and curve arithmetic. -/
def onlinePrefixCost [BN254.FieldCertificate] (output : Option BN254.Point) : Nat :=
  1 + ((onlineInputCost output - 1) + (3 + (7112 + 6405)))

/-- The actual common prefix returns the exact selected memory and charge. -/
theorem onlineMachine_prefix [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (input : BN254.AffineInput) (output : Option BN254.Point) (rest : List Bool)
    (wire : memory.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output output ++ rest) :
    FixedContinuation (onlineMachine attempts) 0 13618 memory
      (onlineCurveMemory memory input output rest) (onlinePrefixCost output) := by
  have setup : FixedContinuation (onlineMachine attempts) 0 1 memory (onlineInputPrepared memory) 1 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineInputSetup
      (onlineBodyLabels 0 1 (by decide) 1) (onlineMachine_inputSetup attempts) memory fuel
  have read : FixedContinuation (onlineMachine attempts) 1 98 (onlineInputPrepared memory)
      (onlineReadMemory memory input output rest) (onlineInputCost output - 1) := by
    intro fuel
    exact onlineInputHost_continue (onlineMachine attempts)
      (fun pc => onlineBodyLabels 1 97 (by decide) 98 pc.val) (onlineMachine_input attempts)
      (onlineInputPrepared memory) input output rest fuel wire
  have originalSetup : FixedContinuation (onlineMachine attempts) 98 101
      (onlineReadMemory memory input output rest)
      (executeLinear onlineOriginalSetup (onlineReadMemory memory input output rest)) 3 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 98 3 (by decide) 101) (onlineMachine_originalSetup attempts)
      (onlineReadMemory memory input output rest) fuel
  have originalStore : FixedContinuation (onlineMachine attempts) 101 7213
      (executeLinear onlineOriginalSetup (onlineReadMemory memory input output rest))
      (onlineOriginalMemory memory input output rest) 7112 := by
    intro fuel
    exact selectedLabelStoreHost_continue (onlineMachine attempts)
      (onlineBodyLabels 101 7112 (by decide) 7213) (onlineMachine_originalStore attempts)
      (executeLinear onlineOriginalSetup (onlineReadMemory memory input output rest)) fuel
  have curve : FixedContinuation (onlineMachine attempts) 7213 13618
      (onlineOriginalMemory memory input output rest) (onlineCurveMemory memory input output rest) 6405 := by
    intro fuel
    exact retargetCurveHost_continue (onlineMachine attempts)
      (onlineBodyLabels 7213 6405 (by decide) 13618) (onlineMachine_curveRetarget attempts)
      (onlineOriginalMemory memory input output rest) fuel
  exact setup.trans _ _ _ _ _ _ _ _ _
    (read.trans _ _ _ _ _ _ _ _ _
      (originalSetup.trans _ _ _ _ _ _ _ _ _ (originalStore.trans _ _ _ _ _ _ _ _ _ curve)))

end Kriterion.ArgoMAC.ArithmeticSimulator
