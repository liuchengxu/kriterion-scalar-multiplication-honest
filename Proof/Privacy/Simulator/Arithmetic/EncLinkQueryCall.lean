import Proof.Privacy.Simulator.Arithmetic.EncLinkQueryTail

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The checked query and tail pass their exact source result to the caller. -/
theorem encLinkBlock_queryCall [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : ContainsEncLink host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := internalForwardReserve attempts count overlayCount (28 + fuel) memory
    run host reserve ⟨labels 7239, memory⟩ =
      (internalForwardSamples attempts count overlayCount memory).bind fun result =>
        (run host (reserve - result.2)
          ⟨labels (encLinkQueryLabels (internalForwardReturn result.1)), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  exact internalForwardBlock_samples host attempts count overlayCount (28 + fuel)
    (labels ∘ encLinkQueryLabels) (encLinkBlock_query host attempts labels present)
    memory attemptFits tableFits overlayFits counter overlayCounter

end Kriterion.ArgoMAC.ArithmeticSimulator
