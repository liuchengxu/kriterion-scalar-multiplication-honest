import Proof.Privacy.Simulator.Arithmetic.PointHornerLoopMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host initializes the Horner accumulator in five instructions. -/
theorem hornerBlock_initialize [BN254.FieldCertificate] (host : Machine) (count : Nat)
    (fits : 22 * count + 5 < 2 ^ 256) (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (fuel : Nat) (base : Memory) :
    run host (fuel + 5) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels (hornerBoundary 0 (Nat.zero_le count)), hornerInitial base⟩).map
        (Option.map fun result => (result.1, result.2 + 5)) := by
  have code0 := present ⟨0, by omega⟩ (by change 0 < 22 * count + 5; omega)
  have code1 := present ⟨1, by omega⟩ (by change 1 < 22 * count + 5; omega)
  have code2 := present ⟨2, by omega⟩ (by change 2 < 22 * count + 5; omega)
  have code3 := present ⟨3, by omega⟩ (by change 3 < 22 * count + 5; omega)
  have code4 := present ⟨4, by omega⟩ (by change 4 < 22 * count + 5; omega)
  simp only [pointHornerMachine, Vector.getElem_ofFn] at code0 code1 code2 code3 code4
  simp at code0 code1 code2 code3 code4
  change run host (fuel + 5) ⟨labels ⟨0, by omega⟩, base⟩ = _
  simp [run, step, code0, code1, code2, code3, code4, relocate, hornerInitial, hornerBoundary,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- Every prefix reads the fixed RAM source and returns its exact arithmetic memory. -/
theorem hornerBlock_prefix [BN254.FieldCertificate] [BN254.GroupCertificate]
    (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (points : List BN254.Point) (length : points.length = count)
    (n : Nat) (inside : n ≤ count) (fuel : Nat) (base : Memory)
    (zero : base.registers 9 = 0) (one : base.registers 12 = 1)
    (input : readPoint base.registers scalarMultiple = some (0 : BN254.Point))
    (source : ∀ i : Fin count, storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * i.val)) =
      some ((points[i.val]?).getD 0)) :
    run host (fuel + n * hornerStepCost) ⟨labels (hornerBoundary 0 (Nat.zero_le count)), base⟩ =
      (run host fuel ⟨labels (hornerBoundary n inside), hornerPrefixMemory points n base⟩).map
        (Option.map fun result => (result.1, result.2 + n * hornerStepCost)) := by
  induction n generalizing fuel with
  | zero =>
      simp only [Nat.zero_mul, Nat.add_zero, hornerPrefixMemory]
      have identity : (Option.map fun result : Configuration (host.size + 1) × Nat => (result.1, result.2)) = id := by
        funext result; cases result <;> rfl
      rw [identity, PMF.map_id]
  | succ n ih =>
      have before : n ≤ count := by omega
      have prior := hornerPrefixMemory_spec points n (by omega) base input
      have fromRam : storedPoint (hornerPrefixMemory points n base).ram
          ((hornerPrefixMemory points n base).registers 10 + BitVec.ofNat 256 (3 * (count - 1 - n))) =
          some ((points[count - 1 - n]?).getD 0) := by
        rw [prior.2.2.1, prior.2.2.2 10 (by decide)]
        exact source ⟨count - 1 - n, by omega⟩
      have next := hornerBlock_step host count fits labels present ⟨n, by omega⟩ fuel
        (hornerPrefixMemory points n base) (pointHorner radix (points.drop (points.length - n)))
        ((points[count - 1 - n]?).getD 0) ((prior.2.2.2 9 (by decide)).trans zero)
        ((prior.2.2.2 12 (by decide)).trans one) prior.1 fromRam
      rw [show fuel + (n + 1) * hornerStepCost = (fuel + hornerStepCost) + n * hornerStepCost by rw [Nat.add_mul]; omega,
        ih before (fuel + hornerStepCost), next]
      simp only [PMF.map_comp, Option.map_map, Function.comp_def]
      have memory : hornerPrefixMemory points (n + 1) base =
          hornerStepMemory (hornerPrefixMemory points n base) (count - 1 - n)
            (pointHorner radix (points.drop (points.length - n))) ((points[count - 1 - n]?).getD 0) := by
        simp only [hornerPrefixMemory, length]
      rw [memory]
      apply congrArg (fun transform => PMF.map transform _)
      funext result
      cases result <;> simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The complete Horner memory includes its fixed initialization. -/
def pointHornerMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) (base : Memory) : Memory :=
  hornerPrefixMemory points points.length (hornerInitial base)

/-- The full block charges every point update and all five initialization instructions. -/
def pointHornerCost (count : Nat) : Nat := count * hornerStepCost + 5

/-- The host returns the exact Horner memory with its unused fuel. -/
theorem pointHornerBlock_run [BN254.FieldCertificate] [BN254.GroupCertificate]
    (host : Machine) (count : Nat) (fits : 22 * count + 5 < 2 ^ 256)
    (labels : Fin (22 * count + 6) → Fin (host.size + 1))
    (present : ContainsPointHorner host count fits labels) (points : List BN254.Point) (length : points.length = count)
    (fuel : Nat) (base : Memory)
    (source : ∀ i : Fin count, storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * i.val)) =
      some ((points[i.val]?).getD 0)) :
    run host (fuel + pointHornerCost count) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels (hornerBoundary count (Nat.le_refl count)), pointHornerMemory points base⟩).map
        (Option.map fun result => (result.1, result.2 + pointHornerCost count)) := by
  have initialSource : ∀ i : Fin count, storedPoint (hornerInitial base).ram
      ((hornerInitial base).registers 10 + BitVec.ofNat 256 (3 * i.val)) = some ((points[i.val]?).getD 0) := by
    simpa [hornerInitial] using source
  rw [show fuel + pointHornerCost count = (fuel + count * hornerStepCost) + 5 by unfold pointHornerCost; omega,
    hornerBlock_initialize host count fits labels present,
    hornerBlock_prefix host count fits labels present points length count (Nat.le_refl count) fuel
      (hornerInitial base) (by simp [hornerInitial]) (by simp [hornerInitial]) (hornerInitial_point base) initialSource]
  have memory : hornerPrefixMemory points count (hornerInitial base) = pointHornerMemory points base := by
    simp only [pointHornerMemory, length]
  rw [memory]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  apply congrArg (fun transform => PMF.map transform _)
  funext result
  cases result <;> simp [pointHornerCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The returned point equals the paper's Horner expression. -/
theorem pointHornerMemory_spec [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) (base : Memory) :
    readPoint (pointHornerMemory points base).registers scalarMultiple = some (pointHorner radix points) ∧
    (pointHornerMemory points base).bits = base.bits ∧
    (pointHornerMemory points base).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val → register ≠ 9 → register ≠ 12 →
      (pointHornerMemory points base).registers register = base.registers register := by
  have spec := hornerPrefixMemory_spec points points.length (Nat.le_refl _) (hornerInitial base) (hornerInitial_point base)
  refine ⟨by simpa only [pointHornerMemory, Nat.sub_self, List.drop_zero] using spec.1,
    spec.2.1, spec.2.2.1, ?_⟩
  intro register caller notNine notTwelve
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  rw [pointHornerMemory, spec.2.2.2 register caller]
  simp only [hornerInitial, Function.update_of_ne (different 7 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne notTwelve, Function.update_of_ne notNine]

/-- Each reverse-order entry uses at most 1553 fixed instructions. -/
theorem hornerStepCost_bound : hornerStepCost ≤ 1553 := by
  have bounded : radix.val < 2 ^ 256 := lt_trans radix.val_lt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
  have scalar := scalarMul_instruction_bound (BitVec.ofNat 256 radix.val)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] at scalar
  unfold hornerStepCost
  omega

/-- The whole block has a linear fixed-instruction bound. -/
theorem pointHornerCost_bound (count : Nat) : pointHornerCost count ≤ 1553 * count + 5 := by
  have scaled := Nat.mul_le_mul_left count hornerStepCost_bound
  unfold pointHornerCost
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
