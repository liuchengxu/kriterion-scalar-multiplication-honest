import Proof.Privacy.Simulator.Arithmetic.InternalForwardCode
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The internal tail charges its flag test and its accepted overlay scan. -/
def internalForwardTail (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 7 = 0#256 then (memory, 1)
  else ((overlayForwardScan count memory).1, (overlayForwardScan count memory).2 + 1)

def internalForwardReturn (memory : Memory) : Fin 199 :=
  if memory.registers 7 = 0#256 then 198 else 197

/-- The internal tail keeps both cutoff and success continuations in the host. -/
theorem internalForwardBlock_tail [BN254.FieldCertificate] (host : Machine)
    (attempts count fuel : Nat) (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) (memory : Memory)
    (fits : count < 2 ^ 256)
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 count)
    (enough : 11 * count + 8 ≤ fuel) :
    run host fuel ⟨labels 178, memory⟩ =
      (run host (fuel - (internalForwardTail count memory).2)
        ⟨labels (internalForwardReturn memory), (internalForwardTail count memory).1⟩).map
          (Option.map fun result => (result.1, result.2 + (internalForwardTail count memory).2)) := by
  have gate : host.code[(labels 178).val] = .branch 7 (labels 198) (labels 179) := by
    simpa [internalForward, relocate] using present 178 (by decide)
  have one : fuel = (fuel - 1) + 1 := by omega
  conv_lhs => rw [one, run]
  simp only [step, gate]
  simp only [show (0 : Word) = 0#256 from rfl]
  by_cases rejected : memory.registers 7 = 0#256
  · simp [rejected, internalForwardTail, internalForwardReturn, PMF.pure_bind]
  · simp only [rejected, ↓reduceIte, PMF.pure_bind]
    have bound := overlayForward_cost count memory
    have available : (overlayForwardScan count memory).2 ≤ fuel - 1 := by omega
    have scanned := overlayForward_continue host (labels ∘ internalOverlayLoadLabels)
      (labels ∘ internalOverlayScanLabels)
      (internalForwardBlock_loader host attempts labels present)
      (internalForwardBlock_scanner host attempts labels present) rfl count memory fits counter
      (fuel - 1 - (overlayForwardScan count memory).2)
    change run host _ ⟨labels 179, memory⟩ = _ at scanned
    rw [show fuel - 1 = (overlayForwardScan count memory).2 +
      (fuel - 1 - (overlayForwardScan count memory).2) by omega, scanned]
    simp [internalForwardTail, internalForwardReturn, rejected, PMF.map_comp, Option.map_map,
      Function.comp_def, internalOverlayScanLabels, Nat.add_assoc, Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]

/-- The reserve includes the stored query, flag test, overlay scan, and caller fuel. -/
def internalForwardReserve (attempts count overlayCount fuel : Nat) (memory : Memory) : Nat :=
  22 + (permutationForwardCost attempts count count (oracleLoaded memory) +
    (3 + (11 * overlayCount + 8 + fuel)))

/-- The internal query implements the stored source and overlay without wire output. -/
theorem internalForwardBlock_continue [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := internalForwardReserve attempts count overlayCount fuel memory
    run host reserve ⟨labels 0, memory⟩ =
      (storedForwardSamples attempts count memory).bind fun result =>
        let tail := internalForwardTail overlayCount result.1
        let charge := result.2 - 1 + tail.2
        (run host (reserve - charge) ⟨labels (internalForwardReturn result.1), tail.1⟩).map
          (Option.map fun final => (final.1, final.2 + charge)) := by
  dsimp only
  have executed := storedForwardBlock_continue host attempts count (11 * overlayCount + 8 + fuel)
    (labels ∘ internalForwardLabels) (internalForwardBlock_stored host attempts labels present)
    memory attemptFits tableFits counter
  change run host (internalForwardReserve attempts count overlayCount fuel memory)
    ⟨labels 0, memory⟩ = _ at executed
  rw [executed]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := storedForwardSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  let remaining := internalForwardReserve attempts count overlayCount fuel memory - (cost - 1)
  have enough : 11 * overlayCount + 8 ≤ remaining := by
    dsimp [remaining, internalForwardReserve]
    omega
  change (run host remaining ⟨labels 178, final⟩).map _ = _
  rw [internalForwardBlock_tail host attempts overlayCount remaining labels present final overlayFits
    (overlayCounter (final, cost) supported) enough]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, remaining, Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
