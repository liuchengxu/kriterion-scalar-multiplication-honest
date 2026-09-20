import Proof.Privacy.Simulator.Arithmetic.PointHornerCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host reads one canonical point from RAM in seven instructions. -/
theorem hornerBlock_load [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 22 * count + 5 < 2 ^ 256) (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (one : base.registers 12 = 1) :
    run host (fuel + 7) ⟨labels (hornerSlot index 11), base⟩ =
      (run host fuel ⟨labels (hornerSlot index 18), hornerLoaded base (count - 1 - index.val)⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  have code := hornerBlock_tail_code host count fits labels present index
  simp [run, step, code 11 (by decide), code 12 (by decide), code 13 (by decide),
    code 14 (by decide), code 15 (by decide), code 16 (by decide), code 17 (by decide),
    relocate, Arithmetic.eval, one, hornerLoaded, Function.update_comm,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The host adds the loaded point and copies the canonical sum in four instructions. -/
theorem hornerBlock_add [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 22 * count + 5 < 2 ^ 256) (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (left right : BN254.Point) (zero : base.registers 9 = 0)
    (accumulator : readPoint base.registers scalarAccumulator = some left)
    (multiple : storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (count - 1 - index.val))) = some right) :
    run host (fuel + 4) ⟨labels (hornerSlot index 18), hornerLoaded base (count - 1 - index.val)⟩ =
      (run host fuel ⟨labels (hornerBoundary (index.val + 1) index.isLt),
        hornerTailMemory base (count - 1 - index.val) left right⟩).map
        (Option.map fun result => (result.1, result.2 + 4)) := by
  have code := hornerBlock_tail_code host count fits labels present index
  have acc := (hornerLoaded_accumulator base (count - 1 - index.val)).trans accumulator
  have mul := (hornerLoaded_point base (count - 1 - index.val)).trans multiple
  have caller : (hornerLoaded base (count - 1 - index.val)).registers 9 = 0 := by simp [hornerLoaded, zero]
  have added : (writePoint (hornerLoaded base (count - 1 - index.val)).registers scalarAccumulator (left + right)) 9 = 0 := by
    rw [writePoint_other _ scalarAccumulator _ 9 (by decide) (by decide) (by decide), caller]
  simp [run, step, code 18 (by decide), code 19 (by decide), code 20 (by decide), code 21 (by decide),
    relocate, acc, mul, Arithmetic.eval, added, hornerTailMemory,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The complete tail adds one RAM point in eleven charged instructions. -/
theorem hornerBlock_tail [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 22 * count + 5 < 2 ^ 256) (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (left right : BN254.Point) (zero : base.registers 9 = 0) (one : base.registers 12 = 1)
    (accumulator : readPoint base.registers scalarAccumulator = some left)
    (multiple : storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (count - 1 - index.val))) = some right) :
    run host (fuel + 11) ⟨labels (hornerSlot index 11), base⟩ =
      (run host fuel ⟨labels (hornerBoundary (index.val + 1) index.isLt),
        hornerTailMemory base (count - 1 - index.val) left right⟩).map
        (Option.map fun result => (result.1, result.2 + 11)) := by
  rw [show fuel + 11 = (fuel + 4) + 7 by omega,
    hornerBlock_load host count fits labels present index _ base one,
    hornerBlock_add host count fits labels present index fuel base left right zero accumulator multiple]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- One Horner entry returns its exact arithmetic memory. -/
def hornerStepMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (index : Nat) (current next : BN254.Point) : Memory :=
  hornerTailMemory (scalarFinish (hornerReady base) current) index (radix • current) next

/-- The fixed radix gives one fixed execution cost for every Horner entry. -/
def hornerStepCost : Nat := scalarLoopCost radix.val + 15

/-- The host executes one Horner entry with its exact cost and RAM source. -/
theorem hornerBlock_step [BN254.FieldCertificate] [BN254.GroupCertificate]
    (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (index : Fin count) (fuel : Nat) (base : Memory)
    (current next : BN254.Point) (zero : base.registers 9 = 0) (one : base.registers 12 = 1)
    (input : readPoint base.registers scalarMultiple = some current)
    (source : storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (count - 1 - index.val))) = some next) :
    run host (fuel + hornerStepCost) ⟨labels (hornerBoundary index.val (Nat.le_of_lt index.isLt)), base⟩ =
      (run host fuel ⟨labels (hornerBoundary (index.val + 1) index.isLt),
        hornerStepMemory base (count - 1 - index.val) current next⟩).map
        (Option.map fun result => (result.1, result.2 + hornerStepCost)) := by
  have i := index.isLt
  have position : 5 + 22 * index.val < 22 * count + 5 := by omega
  have quotient : (5 + 22 * index.val - 5) / 22 = index.val := by omega
  have remainder : (5 + 22 * index.val - 5) % 22 = 0 := by omega
  have code : host.code[(labels (hornerBoundary index.val (Nat.le_of_lt index.isLt))).val] =
      .constant 0 (BitVec.ofNat 256 radix.val) ((labels ∘ hornerScalarLabels index) 0) := by
    rw [present _ position]
    simp [pointHornerMachine, hornerBoundary, position, quotient, remainder,
      show 5 + 22 * index.val ≠ 0 by omega, show 5 + 22 * index.val ≠ 1 by omega,
      show 5 + 22 * index.val ≠ 2 by omega, show 5 + 22 * index.val ≠ 3 by omega,
      show 5 + 22 * index.val ≠ 4 by omega, relocate, Function.comp_def, hornerScalarLabels]
  have ready : readPoint (hornerReady base).registers scalarMultiple = some current := by
    rw [hornerReady, readPoint_update_other base.registers scalarMultiple 0 _ (by decide) (by decide) (by decide)]
    exact input
  have bounded : radix.val < 2 ^ 256 := lt_trans radix.val_lt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
  have value : ((hornerReady base).registers 0).toNat = radix.val := by
    simp only [hornerReady, Function.update_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  have block := scalarMulBlock_memory host (labels ∘ hornerScalarLabels index)
    (hornerBlock_scalar host count fits labels present index) (hornerReady base) current ready
  have continued := run_after_prefix host (scalarLoopCost radix.val + 3) (fuel + 11)
    ⟨(labels ∘ hornerScalarLabels index) 0, hornerReady base⟩
  rw [value] at block
  rw [block, PMF.pure_bind] at continued
  have spec := hornerScaled_spec base current input
  have loaded : storedPoint (scalarFinish (hornerReady base) current).ram
      ((scalarFinish (hornerReady base) current).registers 10 + BitVec.ofNat 256 (3 * (count - 1 - index.val))) = some next := by
    rw [spec.2.2.1, spec.2.2.2 10 (by decide)]
    exact source
  have tail := hornerBlock_tail host count fits labels present index fuel
    (scalarFinish (hornerReady base) current) (radix • current) next
    ((spec.2.2.2 9 (by decide)).trans zero) ((spec.2.2.2 12 (by decide)).trans one) spec.1 loaded
  have total : fuel + hornerStepCost = (scalarLoopCost radix.val + 3 + (fuel + 11)) + 1 := by
    unfold hornerStepCost; omega
  rw [total, run, step, code]
  simp only [PMF.pure_bind]
  change (run host (scalarLoopCost radix.val + 3 + (fuel + 11))
    ⟨(labels ∘ hornerScalarLabels index) 0, hornerReady base⟩).map _ = _
  rw [continued]
  change ((run host (fuel + 11) ⟨labels (hornerSlot index 11), scalarFinish (hornerReady base) current⟩).map _).map _ = _
  rw [tail]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  apply congrArg (fun transform => PMF.map transform
    (run host fuel ⟨labels (hornerBoundary (index.val + 1) index.isLt),
      hornerStepMemory base (count - 1 - index.val) current next⟩))
  funext result
  cases result <;> simp [hornerStepCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

end Kriterion.ArgoMAC.ArithmeticSimulator
