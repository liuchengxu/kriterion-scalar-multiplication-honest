import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Caller fuel increases the checked slot reserve by exactly the same amount. -/
theorem checkedSlotReserve_add (attempts count overlayCount historyCount fuel : Nat) (memory : Memory) :
    checkedSlotReserve attempts count overlayCount historyCount fuel memory =
      checkedSlotReserve attempts count overlayCount historyCount 0 memory + fuel := by
  simp only [checkedSlotReserve, checkedSlotBranchReserve]
  split <;> simp [internalForwardReserve, Nat.add_assoc]
  omega

/-- A common table-length bound gives a fixed executed-instruction reserve. -/
def checkedSlotRunBudget (attempts limit : Nat) : Nat := 2574 * attempts + 56 * limit + 206

theorem checkedSlotReserve_uniform (attempts count overlayCount historyCount limit : Nat) (memory : Memory)
    (used : count ≤ limit) (overlay : overlayCount ≤ limit) (history : historyCount ≤ limit) :
    checkedSlotReserve attempts count overlayCount historyCount 0 memory ≤ checkedSlotRunBudget attempts limit := by
  have bound := checkedSlotReserve_budget attempts count overlayCount historyCount 0 memory
  change 304 + 1 + _ ≤ _ at bound
  unfold checkedSlotRunBudget
  omega

/-- Any larger caller budget retains the same exact checked source law. -/
theorem checkedSlotBlock_budgeted [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount historyCount budget : Nat) (labels : Fin 305 → Fin (host.size + 1))
    (present : ContainsCheckedSlot host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256) (historyFits : historyCount < 2 ^ 256)
    (historyCounter : (executeLinear checkedSlotStart memory).ram
      (historyHeader (executeLinear checkedSlotStart memory)) = BitVec.ofNat 256 historyCount)
    (counter : (oracleLoaded (checkedSlotRestored (checkedSlotPrepared historyCount memory))).registers 0 =
      BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count
      (checkedSlotRestored (checkedSlotPrepared historyCount memory))).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount)
    (enough : checkedSlotReserve attempts count overlayCount historyCount 0 memory ≤ budget) :
    run host budget ⟨labels 0, memory⟩ =
      (checkedSlotSamples attempts count overlayCount historyCount memory).bind fun result =>
        (run host (budget - result.2.2) ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  have executed := checkedSlotBlock_continue host attempts count overlayCount historyCount
    (budget - checkedSlotReserve attempts count overlayCount historyCount 0 memory) labels present memory
    attemptFits tableFits overlayFits historyFits historyCounter counter overlayCounter
  dsimp only at executed
  rw [checkedSlotReserve_add, Nat.add_sub_cancel' enough] at executed
  exact executed

end Kriterion.ArgoMAC.ArithmeticSimulator
