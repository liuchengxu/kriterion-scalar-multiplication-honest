import Proof.Privacy.Simulator.Arithmetic.CheckedSlotForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

theorem checkedSource_shiftCharge {S A : Type} (samples : PMF S) (charge : S → Nat)
    (continuation : S → Nat → PMF (Option (A × Nat))) (reserve extraCharge : Nat) :
    (samples.bind fun value => (continuation value (reserve - charge value)).map
      (Option.map fun result => (result.1, result.2 + charge value))).map
        (Option.map fun result => (result.1, result.2 + extraCharge)) =
    samples.bind fun value => (continuation value ((extraCharge + reserve) - (extraCharge + charge value))).map
      (Option.map fun result => (result.1, result.2 + (extraCharge + charge value))) := by
  rw [PMF.map_bind]
  apply congrArg (PMF.bind samples)
  funext value
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm]
  rw [show reserve + extraCharge - (extraCharge + charge value) = reserve - charge value by omega]
  simp only [Nat.add_left_comm extraCharge]

/-- The accepted branch restores the command in six fixed instructions. -/
theorem checkedSlotBlock_accept_prefix [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels)
    (memory : Memory) (accepted : memory.registers 7 ≠ 0) :
    run host (6 + fuel) ⟨labels 55, memory⟩ =
      (run host fuel ⟨labels 61, checkedSlotRestored memory⟩).map
        (Option.map fun result => (result.1, result.2 + 6)) := by
  have branch : host.code[(labels 55).val] = .branch 7 (labels 301) (labels 56) := by
    simpa [checkedSlot, relocate] using present 55 (by decide) (by decide)
  have restored := linear_continue host checkedSlotRestore (labels ∘ checkedSlotRestoreLabels)
    (checkedSlotBlock_restore host attempts labels present) memory fuel
  simp only [show checkedSlotRestore.length = 5 from rfl, checkedSlotRestore_memory] at restored
  change run host (5 + fuel) ⟨labels 56, memory⟩ = _ at restored
  rw [show 6 + fuel = (5 + fuel) + 1 by omega, run]
  simp only [step, branch, accepted, ↓reduceIte, PMF.pure_bind]
  rw [restored]
  change ((run host fuel ⟨labels 61, checkedSlotRestored memory⟩).map _).map _ = _
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The colliding branch records bad in four fixed instructions. -/
theorem checkedSlotBlock_reject_prefix [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 305 → Fin (host.size + 1)) (present : ContainsCheckedSlot host attempts labels)
    (memory : Memory) (collision : memory.registers 7 = 0) :
    run host (4 + fuel) ⟨labels 55, memory⟩ =
      (run host fuel ⟨labels 300, executeLinear checkedSlotCollision memory⟩).map
        (Option.map fun result => (result.1, result.2 + 4)) := by
  have branch : host.code[(labels 55).val] = .branch 7 (labels 301) (labels 56) := by
    simpa [checkedSlot, relocate] using present 55 (by decide) (by decide)
  rw [show 4 + fuel = (3 + fuel) + 1 by omega, run]
  simp only [step, branch, collision, ↓reduceIte, PMF.pure_bind]
  rw [checkedSlotBlock_collision_return host attempts labels present]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The branch source skips one collision or executes one accepted command. -/
noncomputable def checkedSlotBranchSamples (attempts count overlayCount : Nat) (memory : Memory) :
    PMF (Fin 305 × Memory × Nat) :=
  if memory.registers 7 = 0 then PMF.pure (300, executeLinear checkedSlotCollision memory, 4)
  else (storedForwardSamples attempts count (checkedSlotRestored memory)).map fun result =>
    (checkedSlotForwardReturn result.1, checkedSlotForwardResult overlayCount result.1,
      6 + checkedSlotForwardCost overlayCount result)

/-- The branch reserve includes its test, restore, private query, and successful finish. -/
def checkedSlotBranchReserve (attempts count overlayCount fuel : Nat) (memory : Memory) : Nat :=
  if memory.registers 7 = 0 then 4 + fuel
  else 6 + internalForwardReserve attempts count overlayCount (40 + fuel) (checkedSlotRestored memory)


/-- The branch returns its exact source law through the normal or cutoff continuation. -/
theorem checkedSlotBlock_branch [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 305 → Fin (host.size + 1))
    (present : ContainsCheckedSlot host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded (checkedSlotRestored memory)).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count (checkedSlotRestored memory)).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := checkedSlotBranchReserve attempts count overlayCount fuel memory
    run host reserve ⟨labels 55, memory⟩ =
      (checkedSlotBranchSamples attempts count overlayCount memory).bind fun (result : Fin 305 × Memory × Nat) =>
        (run host (reserve - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  dsimp only
  by_cases collision : memory.registers 7 = 0
  · simp only [checkedSlotBranchReserve, checkedSlotBranchSamples, if_pos collision, PMF.pure_bind]
    rw [checkedSlotBlock_reject_prefix host attempts fuel labels present memory collision]
    simp
  · simp only [checkedSlotBranchReserve, checkedSlotBranchSamples, if_neg collision]
    rw [checkedSlotBlock_accept_prefix host attempts _ labels present memory collision,
      checkedSlotBlock_forward_return host attempts count overlayCount fuel labels present
        (checkedSlotRestored memory) attemptFits tableFits overlayFits counter overlayCounter]
    rw [PMF.bind_map]
    exact checkedSource_shiftCharge (storedForwardSamples attempts count (checkedSlotRestored memory))
      (checkedSlotForwardCost overlayCount)
      (fun result remaining => run host remaining
        ⟨labels (checkedSlotForwardReturn result.1), checkedSlotForwardResult overlayCount result.1⟩)
      (internalForwardReserve attempts count overlayCount (40 + fuel) (checkedSlotRestored memory)) 6

end Kriterion.ArgoMAC.ArithmeticSimulator
