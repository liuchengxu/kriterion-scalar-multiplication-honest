import Proof.Privacy.Simulator.Arithmetic.GateDriverHostCode
import Proof.Privacy.Simulator.Arithmetic.CheckedSlotSampleCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The slot source loads its saved command before it checks freshness. -/
noncomputable def gateDriverSlotSamples (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) : PMF (Fin 305 × Memory × Nat) :=
  (checkedSlotAutomaticSamples attempts (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory)).map
    fun result => (result.1, result.2.1, 8 + result.2.2)

/-- The caller bounds the stored tables for the selected slot. -/
def GateDriverSlotReady (attempts limit : Nat) (gate : GateCode) (slot : Fin 3) (memory : Memory) : Prop :=
  CheckedSlotReady attempts limit (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory)

/-- The host loads one command and runs its checked slot. -/
theorem gateSlotHost_continue [BN254.FieldCertificate] (host : Machine) (attempts limit fuel : Nat)
    (gate : GateCode) (slot : Fin 3) (loadLabels : Nat → Fin (host.size + 1))
    (slotLabels : Fin 305 → Fin (host.size + 1))
    (hasLoad : ContainsLinear host (gateSlotLoad (gate.oracle slot) slot) loadLabels)
    (hasSlot : ContainsCheckedSlot host attempts slotLabels) (join : loadLabels 8 = slotLabels 0)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256)
    (ready : GateDriverSlotReady attempts limit gate slot memory) :
    run host (8 + checkedSlotRunBudget attempts limit + fuel) ⟨loadLabels 0, memory⟩ =
      (gateDriverSlotSamples attempts gate slot memory).bind fun result =>
        (run host (8 + checkedSlotRunBudget attempts limit + fuel - result.2.2)
          ⟨slotLabels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  have loaded :=  linear_continue host (gateSlotLoad (gate.oracle slot) slot) loadLabels hasLoad memory
    (checkedSlotRunBudget attempts limit + fuel)
  change run host (8 + (checkedSlotRunBudget attempts limit + fuel)) ⟨loadLabels 0, memory⟩ = _ at loaded
  rw [show 8 + checkedSlotRunBudget attempts limit + fuel = 8 + (checkedSlotRunBudget attempts limit + fuel) by omega, loaded]
  simp only [show (gateSlotLoad (gate.oracle slot) slot).length = 8 from rfl, join]
  rw [checkedSlotBlock_automatic host attempts limit fuel slotLabels hasSlot _ attemptFits ready]
  simp only [gateDriverSlotSamples, PMF.bind_map]
  exact checkedSource_shiftCharge (checkedSlotAutomaticSamples attempts (executeLinear (gateSlotLoad (gate.oracle slot) slot) memory))
    (fun result => result.2.2) (fun result remaining => run host remaining ⟨slotLabels result.1, result.2.1⟩)
    (checkedSlotRunBudget attempts limit + fuel) 8

/-- Every loaded slot returns normally or returns sampler cutoff within its reserve. -/
theorem gateDriverSlotSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode)
    (slot : Fin 3) (memory : Memory) (result : Fin 305 × Memory × Nat)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverSlotReady attempts limit gate slot memory)
    (supported : result ∈ (gateDriverSlotSamples attempts gate slot memory).support) :
    result.2.2 ≤ 8 + checkedSlotRunBudget attempts limit ∧ (result.1 = 300 ∨ result.1 = 304) := by
  obtain ⟨draw, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have bound := checkedSlotAutomaticSamples_cost attempts limit _ draw attemptFits ready member
  exact ⟨Nat.add_le_add_left bound.1 8, bound.2⟩

/-- Each gate slot uses the same checked source law in its host. -/
theorem gateDriverBlock_slot [BN254.FieldCertificate] (host : Machine) (attempts limit fuel : Nat)
    (gate : GateCode) (labels : Fin 1036 → Fin (host.size + 1))
    (present : ContainsGateDriver host attempts gate labels) (slot : Fin 3) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : GateDriverSlotReady attempts limit gate slot memory) :
    run host (8 + checkedSlotRunBudget attempts limit + fuel)
      ⟨labels (gateDriverSlotLoadLabels slot 0), memory⟩ =
      (gateDriverSlotSamples attempts gate slot memory).bind fun result =>
        (run host (8 + checkedSlotRunBudget attempts limit + fuel - result.2.2)
          ⟨labels (gateDriverSlotLabels slot result.1), result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  apply gateSlotHost_continue host attempts limit fuel gate slot
    (labels ∘ gateDriverSlotLoadLabels slot) (labels ∘ gateDriverSlotLabels slot)
  · fin_cases slot
    · exact gateDriverBlock_load0 host attempts gate labels present
    · exact gateDriverBlock_load1 host attempts gate labels present
    · exact gateDriverBlock_load2 host attempts gate labels present
  · fin_cases slot
    · exact gateDriverBlock_slot0 host attempts gate labels present
    · exact gateDriverBlock_slot1 host attempts gate labels present
    · exact gateDriverBlock_slot2 host attempts gate labels present
  · fin_cases slot <;> rfl
  · exact attemptFits
  · exact ready

end Kriterion.ArgoMAC.ArithmeticSimulator
