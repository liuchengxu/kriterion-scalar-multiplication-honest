import Proof.Privacy.Simulator.Arithmetic.EncLinkRead
import Proof.Privacy.Simulator.Arithmetic.EncLinkQueryBody
import Proof.Privacy.Simulator.Arithmetic.ChargedContinuation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- One iteration consumes one scheduled index and retains its full charged source result. -/
noncomputable def encLinkIterationSamples (attempts count overlayCount : Nat)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) : PMF (Memory × Nat × Fin 7468) :=
  (encLinkQuerySamples attempts count overlayCount (encLinkPrepared memory index rest)).map (chargedResult 121)


/-- The iteration reserve includes the reader, query, output write, and controller. -/
noncomputable def encLinkIterationReserve (attempts count overlayCount fuel : Nat)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) : Nat :=
  121 + internalForwardReserve attempts count overlayCount (28 + fuel) (encLinkPrepared memory index rest)

/-- The actual loop body implements one complete source iteration in any host. -/
theorem encLinkBlock_iteration [BN254.FieldCertificate] (host : Machine) (attempts count overlayCount fuel : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = encLinkIndexBits index ++ rest)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded (encLinkPrepared memory index rest)).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count (encLinkPrepared memory index rest)).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := encLinkIterationReserve attempts count overlayCount fuel memory index rest
    run host reserve ⟨labels 7208, memory⟩ =
      (encLinkIterationSamples attempts count overlayCount memory index rest).bind fun result =>
        (run host (reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.1)) := by
  dsimp only [encLinkIterationReserve]
  rw [run_after_prefix, encLinkBlock_read host attempts labels present memory index rest wire, PMF.pure_bind]
  dsimp only
  have queried := encLinkBlock_queryBody host attempts count overlayCount fuel labels present
    (encLinkPrepared memory index rest) attemptFits tableFits overlayFits counter overlayCounter
  dsimp only at queried
  rw [queried]
  exact chargedContinuation host labels
    (encLinkQuerySamples attempts count overlayCount (encLinkPrepared memory index rest)) 121 _

end Kriterion.ArgoMAC.ArithmeticSimulator
