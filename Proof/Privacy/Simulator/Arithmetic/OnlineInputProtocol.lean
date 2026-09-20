import Proof.Privacy.Simulator.Arithmetic.OnlineInputMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- The output value determines the parsed tag and output coordinates. -/
def onlineOutputWords [FieldCertificate] : Option Point → Nat × Nat × Nat
  | none => (0, 0, 0)
  | some .zero => (2, 0, 0)
  | some (.some (x := x) (y := y) _) => (1, x.val, y.val)

/-- The output value determines the complete reader cost. -/
def onlineInputCost [FieldCertificate] : Option Point → Nat
  | some (.some _ _ _) => 7175
  | _ => 3608

/-- The source memory retains every parsed coordinate and the unread suffix. -/
def onlineInputMemory [FieldCertificate] (base : Memory) (input : AffineInput)
    (result : Option Point) (rest : List Bool) : Memory :=
  match result with
  | none => onlineNullMemory base input.x.val input.y.val 0 rest
  | some .zero => onlineNullMemory base input.x.val input.y.val 2 rest
  | some (.some (x := x) (y := y) _) =>
      onlineAffineMemory base input.x.val input.y.val x.val y.val rest

/-- The reader consumes the exact online protocol body. -/
theorem onlineInput_run [FieldCertificate] (base : Memory) (input : AffineInput)
    (result : Option Point) (rest : List Bool)
    (wire : base.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output result ++ rest) :
    run onlineInput (onlineInputCost result) ⟨0, base⟩ =
      PMF.pure (some (⟨97, onlineInputMemory base input result rest⟩, onlineInputCost result)) := by
  cases result with
  | none =>
      exact onlineInput_nullRun base input.x.val input.y.val 0 rest (by decide) (by decide)
        (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
          show bits 2 0 = [false, false] from rfl, List.append_assoc] using wire)
  | some result =>
      cases result with
      | zero =>
          exact onlineInput_nullRun base input.x.val input.y.val 2 rest (by decide) (by decide)
            (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
              show bits 2 2 = [false, true] from rfl, List.append_assoc] using wire)
      | @some x y valid =>
          exact onlineInput_affineRun base input.x.val input.y.val x.val y.val rest
            (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
              show bits 2 1 = [true, false] from rfl, List.append_assoc] using wire)

/-- Every protocol field appears in the exact five-word record. -/
theorem onlineInputMemory_values [FieldCertificate] (base : Memory) (input : AffineInput)
    (result : Option Point) (rest : List Bool) :
    let words := onlineOutputWords result
    let memory := onlineInputMemory base input result rest
    memory.ram = onlineRecordRam base input.x.val input.y.val words.1 words.2.1 words.2.2 ∧
    memory.registers 10 = base.registers 10 ∧ memory.bits 0 = rest := by
  have fieldFits (value : BaseField) : value.val < 2 ^ 254 :=
    lt_trans value.val_lt (by decide : baseFieldModulus < 2 ^ 254)
  cases result with
  | none => exact onlineNullMemory_values base _ _ _ rest (fieldFits _) (fieldFits _) (by decide)
  | some result =>
      cases result with
      | zero => exact onlineNullMemory_values base _ _ _ rest (fieldFits _) (fieldFits _) (by decide)
      | @some x y valid =>
          exact onlineAffineMemory_values base _ _ _ _ rest
            (fieldFits _) (fieldFits _) (fieldFits _) (fieldFits _)

/-- The online reader meets the complete protocol body interface. -/
theorem onlineInput_protocol [FieldCertificate] (base : Memory) (input : AffineInput)
    (result : Option Point) (rest : List Bool)
    (wire : base.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output result ++ rest) :
    (run onlineInput (onlineInputCost result) ⟨0, base⟩).map (Option.map fun result =>
      (result.1.memory.ram, result.1.memory.registers 10, result.1.memory.bits 0, result.2)) =
      PMF.pure (some (onlineRecordRam base input.x.val input.y.val (onlineOutputWords result).1
        (onlineOutputWords result).2.1 (onlineOutputWords result).2.2,
        base.registers 10, rest, onlineInputCost result)) := by
  rw [onlineInput_run base input result rest wire, PMF.pure_map]
  obtain ⟨ram, address, suffix⟩ := onlineInputMemory_values base input result rest
  simp only [Option.map_some, ram, address, suffix]

/-- The reader uses at most 7273 units including its instruction table. -/
theorem onlineInput_budget [FieldCertificate] (result : Option Point) :
    onlineInput.size + 1 + onlineInputCost result ≤ 7273 := by
  cases result with
  | none => norm_num [onlineInputCost, show onlineInput.size = 97 from rfl]
  | some result => cases result <;> norm_num [onlineInputCost, show onlineInput.size = 97 from rfl]

end Kriterion.ArgoMAC.ArithmeticSimulator
