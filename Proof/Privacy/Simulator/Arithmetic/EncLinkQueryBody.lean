import Proof.Privacy.Simulator.Arithmetic.EncLinkQueryCall

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The postprocessing map retains the query charge and its next loop label. -/
def encLinkQueryPost (result : Memory × Nat) : Memory × Nat × Fin 7468 :=
  let tail := encLinkAfterQuery result.1
  (tail.1, result.2 + tail.2.1, tail.2.2)

/-- The query body retains the complete oracle sample, label write, and loop target. -/
noncomputable def encLinkQuerySamples (attempts count overlayCount : Nat) (memory : Memory) :
    PMF (Memory × Nat × Fin 7468) :=
  (internalForwardSamples attempts count overlayCount memory).map encLinkQueryPost

/-- A mapped source uses pointwise caller laws on its supported samples. -/
theorem mappedContinuation {Source Target Result : Type} (source : PMF Source)
    (post : Source → Target) (first : Source → PMF Result) (second : Target → PMF Result)
    (same : ∀ result ∈ source.support, first result = second (post result)) :
    source.bind first = (source.map post).bind second := by
  rw [PMF.bind_map]
  exact Security.ThreePhase.bind_eq_on_support source first (second ∘ post) same

/-- The query postprocessing map has the checked caller law. -/
theorem encLinkBlock_queryPost [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (result : Memory × Nat) (reserve : Nat) (enough : 28 ≤ reserve - result.2) :
    (run host (reserve - result.2)
      ⟨labels (encLinkQueryLabels (internalForwardReturn result.1)), result.1⟩).map
      (Option.map fun final => (final.1, final.2 + result.2)) =
    (run host (reserve - (encLinkQueryPost result).2.1)
      ⟨labels (encLinkQueryPost result).2.2, (encLinkQueryPost result).1⟩).map
      (Option.map fun final => (final.1, final.2 + (encLinkQueryPost result).2.1)) := by
  exact encLinkBlock_queryOutcome host attempts labels present result.1 reserve result.2 enough

/-- The checked query and tail pass their exact source result to the caller. -/
theorem encLinkBlock_queryBody [BN254.FieldCertificate] (host : Machine)
    (attempts count overlayCount fuel : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : ContainsEncLink host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    let reserve := internalForwardReserve attempts count overlayCount (28 + fuel) memory
    run host reserve ⟨labels 7239, memory⟩ =
      (encLinkQuerySamples attempts count overlayCount memory).bind fun result =>
        (run host (reserve - result.2.1) ⟨labels result.2.2, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.1)) := by
  dsimp only
  apply Eq.trans (encLinkBlock_queryCall host attempts count overlayCount fuel labels present memory
    attemptFits tableFits overlayFits counter overlayCounter)
  apply mappedContinuation (internalForwardSamples attempts count overlayCount memory) encLinkQueryPost
  intro result supported
  have bounded := internalForwardSamples_cost attempts count overlayCount memory
    result.1 result.2 attemptFits tableFits counter supported
  have budgetAdd : internalForwardReserve attempts count overlayCount (28 + fuel) memory =
      internalForwardReserve attempts count overlayCount 0 memory + (28 + fuel) := by
    unfold internalForwardReserve
    omega
  exact encLinkBlock_queryPost host attempts labels present result
    (internalForwardReserve attempts count overlayCount (28 + fuel) memory) (by omega)

end Kriterion.ArgoMAC.ArithmeticSimulator
