import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The overlay preserves the acceptance flag used by the caller. -/
theorem internalForwardReturn_tail (count : Nat) (memory : Memory) :
    internalForwardReturn (internalForwardTail count memory).1 = internalForwardReturn memory := by
  unfold internalForwardReturn
  rw [(internalForwardTail_data count memory).2.2]

/-- The compiled internal query returns its complete charged source sample. -/
theorem internalForwardBlock_samples [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 199 → Fin (host.size + 1))
    (present : ContainsInternalForward host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := internalForwardReserve attempts count overlayCount fuel memory
    run host reserve ⟨labels 0, memory⟩ =
      (internalForwardSamples attempts count overlayCount memory).bind fun result =>
        (run host (reserve - result.2) ⟨labels (internalForwardReturn result.1), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  simpa only [internalForwardSamples, PMF.bind_map, Function.comp_def, internalForwardReturn_tail] using
    internalForwardBlock_continue host attempts count overlayCount fuel labels present memory
      attemptFits tableFits overlayFits counter overlayCounter

/-- Each complete internal sample stays within its reserve before caller fuel. -/
theorem internalForwardSamples_cost [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory final : Memory) (cost : Nat) (attemptFits : attempts < 2 ^ 256)
    (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support) :
    cost ≤ internalForwardReserve attempts count overlayCount 0 memory := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have stored := storedForwardSamples_cost attempts count memory before spent attemptFits tableFits counter member
  have overlay := overlayForward_cost overlayCount before
  unfold internalForwardTail
  split <;> dsimp [internalForwardReserve] <;> omega

end Kriterion.ArgoMAC.ArithmeticSimulator
