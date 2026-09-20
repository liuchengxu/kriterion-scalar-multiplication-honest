import Proof.Privacy.Simulator.Arithmetic.CheckedSlotFinish

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The accepted command installs its override only after a successful private query. -/
def checkedSlotForwardResult (overlayCount : Nat) (memory : Memory) : Memory :=
  let tail := (internalForwardTail overlayCount memory).1
  if memory.registers 7 = 0 then tail else checkedSlotFinished tail

/-- The accepted command charges the private query, overlay scan, and successful finish. -/
def checkedSlotForwardCost (overlayCount : Nat) (result : Memory × Nat) : Nat :=
  result.2 - 1 + (internalForwardTail overlayCount result.1).2 +
    if result.1.registers 7 = 0 then 0 else 40

/-- The accepted command returns a separate cutoff continuation. -/
def checkedSlotForwardReturn (memory : Memory) : Fin 305 :=
  if memory.registers 7 = 0 then 304 else 300

/-- Every accepted command retains enough reserve for its forty-instruction finish. -/
theorem checkedSlotForward_enough [BN254.FieldCertificate] (attempts count overlayCount fuel : Nat)
    (memory final : Memory) (cost : Nat) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support) :
    cost - 1 + (internalForwardTail overlayCount final).2 + 40 + fuel ≤
      internalForwardReserve attempts count overlayCount (40 + fuel) memory := by
  have bound := storedForwardSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  have overlay := overlayForward_cost overlayCount final
  unfold internalForwardTail internalForwardReserve
  split <;> dsimp only <;> omega

/-- The internal call installs the checked command and returns its exact source state. -/
theorem checkedSlotBlock_forward_return [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 305 → Fin (host.size + 1))
    (present : ContainsCheckedSlot host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := internalForwardReserve attempts count overlayCount (40 + fuel) memory
    run host reserve ⟨labels 61, memory⟩ =
      (storedForwardSamples attempts count memory).bind fun result =>
        (run host (reserve - checkedSlotForwardCost overlayCount result)
          ⟨labels (checkedSlotForwardReturn result.1), checkedSlotForwardResult overlayCount result.1⟩).map
          (Option.map fun final => (final.1, final.2 + checkedSlotForwardCost overlayCount result)) := by
  dsimp only
  have executed := internalForwardBlock_continue host attempts count overlayCount (40 + fuel)
    (labels ∘ checkedSlotForwardLabels) (checkedSlotBlock_forward host attempts labels present)
    memory attemptFits tableFits overlayFits counter overlayCounter
  change run host (internalForwardReserve attempts count overlayCount (40 + fuel) memory)
    ⟨labels 61, memory⟩ = _ at executed
  rw [executed]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have enough := checkedSlotForward_enough attempts count overlayCount fuel memory final cost
    attemptFits tableFits counter supported
  by_cases failed : final.registers 7 = 0
  · simp only [internalForwardReturn, show (0#256 : Word) = (0 : Word) from rfl, failed, ↓reduceIte, Function.comp_apply,
      checkedSlotForwardLabels, checkedSlotForwardReturn, checkedSlotForwardResult,
      checkedSlotForwardCost, Nat.add_zero]
    rfl
  · simp only [internalForwardReturn, show (0#256 : Word) = (0 : Word) from rfl, failed, ↓reduceIte, Function.comp_apply,
      checkedSlotForwardLabels, checkedSlotForwardReturn, checkedSlotForwardResult,
      checkedSlotForwardCost]
    let reserve := internalForwardReserve attempts count overlayCount (40 + fuel) memory
    let charge := cost - 1 + (internalForwardTail overlayCount final).2
    change (run host (reserve - charge) ⟨labels 260, (internalForwardTail overlayCount final).1⟩).map _ = _
    have room : 40 ≤ reserve - charge := by dsimp [reserve, charge]; omega
    rw [show reserve - charge = 40 + (reserve - charge - 40) by omega,
      checkedSlotBlock_finish host attempts labels present]
    simp [PMF.map_comp, Option.map_map, Function.comp_def, reserve, charge, Nat.sub_sub,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
