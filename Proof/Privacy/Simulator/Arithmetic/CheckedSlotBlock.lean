import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBranch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The preparation executes the fixed start and the complete freshness scan. -/
def checkedSlotPrepared (historyCount : Nat) (memory : Memory) : Memory :=
  (historyFreshSource historyCount (executeLinear checkedSlotStart memory)).1

/-- The prefix charge includes all twelve start instructions and the freshness scan. -/
def checkedSlotPrefixCost (historyCount : Nat) (memory : Memory) : Nat :=
  12 + (historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2

/-- The complete source skips collisions and retains every accepted command effect. -/
noncomputable def checkedSlotSamples (attempts count overlayCount historyCount : Nat) (memory : Memory) :
    PMF (Fin 305 × Memory × Nat) :=
  (checkedSlotBranchSamples attempts count overlayCount (checkedSlotPrepared historyCount memory)).map fun result =>
    (result.1, result.2.1, checkedSlotPrefixCost historyCount memory + result.2.2)

/-- The complete reserve includes every fixed and variable instruction block. -/
def checkedSlotReserve (attempts count overlayCount historyCount fuel : Nat) (memory : Memory) : Nat :=
  checkedSlotPrefixCost historyCount memory +
    checkedSlotBranchReserve attempts count overlayCount fuel (checkedSlotPrepared historyCount memory)

/-- The full checked slot machine implements its source law in any host. -/
theorem checkedSlotBlock_continue [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount historyCount fuel : Nat) (labels : Fin 305 → Fin (host.size + 1))
    (present : ContainsCheckedSlot host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256) (historyFits : historyCount < 2 ^ 256)
    (historyCounter : (executeLinear checkedSlotStart memory).ram
      (historyHeader (executeLinear checkedSlotStart memory)) = BitVec.ofNat 256 historyCount)
    (counter : (oracleLoaded (checkedSlotRestored (checkedSlotPrepared historyCount memory))).registers 0 =
      BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count
      (checkedSlotRestored (checkedSlotPrepared historyCount memory))).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := checkedSlotReserve attempts count overlayCount historyCount fuel memory
    run host reserve ⟨labels 0, memory⟩ =
      (checkedSlotSamples attempts count overlayCount historyCount memory).bind fun result =>
        (run host (reserve - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  dsimp only
  let tailFuel := checkedSlotBranchReserve attempts count overlayCount fuel (checkedSlotPrepared historyCount memory)
  have started := linear_continue host checkedSlotStart (labels ∘ checkedSlotStartLabels)
    (checkedSlotBlock_start host attempts labels present) memory
    ((historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2 + tailFuel)
  simp only [show checkedSlotStart.length = 12 from rfl] at started
  change run host (12 + ((historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2 + tailFuel))
    ⟨labels 0, memory⟩ = _ at started
  have fresh := historyFreshBlock_continue host (labels ∘ checkedSlotFreshLabels)
    (checkedSlotBlock_fresh host attempts labels present) historyCount (executeLinear checkedSlotStart memory)
    historyFits historyCounter tailFuel
  change run host ((historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2 + tailFuel)
    ⟨labels 12, executeLinear checkedSlotStart memory⟩ = _ at fresh
  have cost : checkedSlotReserve attempts count overlayCount historyCount fuel memory =
      12 + ((historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2 + tailFuel) := by
    simp [checkedSlotReserve, checkedSlotPrefixCost, tailFuel, Nat.add_assoc]
  rw [cost, started]
  change (run host _ ⟨labels 12, executeLinear checkedSlotStart memory⟩).map _ = _
  rw [fresh]
  change ((run host tailFuel ⟨labels 55, checkedSlotPrepared historyCount memory⟩).map _).map _ = _
  rw [checkedSlotBlock_branch host attempts count overlayCount fuel labels present
    (checkedSlotPrepared historyCount memory) attemptFits tableFits overlayFits counter overlayCounter,
    PMF.map_bind, PMF.map_bind]
  simp only [checkedSlotSamples, PMF.bind_map, Function.comp_def]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  simp [PMF.map_comp, Option.map_map, Function.comp_def, checkedSlotPrefixCost, tailFuel,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact congrArg (fun remaining => (run host remaining ⟨labels result.1, result.2.1⟩).map
    (Option.map fun final => (final.1, final.2 +
      (result.2.2 + (12 + (historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2)))))
    (show checkedSlotBranchReserve attempts count overlayCount fuel (checkedSlotPrepared historyCount memory) - result.2.2 =
      12 + (checkedSlotBranchReserve attempts count overlayCount fuel (checkedSlotPrepared historyCount memory) +
        (historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2) -
        (result.2.2 + (12 + (historyFreshSource historyCount (executeLinear checkedSlotStart memory)).2)) by omega)

/-- The complete reserve has a concrete linear bound in all stored table lengths. -/
theorem checkedSlotReserve_budget (attempts count overlayCount historyCount fuel : Nat) (memory : Memory) :
    (checkedSlot attempts).size + 1 + checkedSlotReserve attempts count overlayCount historyCount fuel memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 12 * historyCount + 511 + fuel := by
  have fresh := historyFreshSource_cost historyCount (executeLinear checkedSlotStart memory)
  have forward := internalForwardReserve_bound attempts count overlayCount (40 + fuel)
    (checkedSlotRestored (checkedSlotPrepared historyCount memory))
  change 198 + 1 + _ ≤ _ at forward
  change 304 + 1 + _ ≤ _
  unfold checkedSlotReserve checkedSlotPrefixCost checkedSlotBranchReserve
  split <;> omega

end Kriterion.ArgoMAC.ArithmeticSimulator
