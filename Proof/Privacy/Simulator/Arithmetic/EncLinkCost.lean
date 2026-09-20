import Proof.Privacy.Simulator.Arithmetic.EncLinkIteration

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every tail uses at most its reserved 28 instructions. -/
theorem encLinkAfterQuery_cost (memory : Memory) : (encLinkAfterQuery memory).2.1 ≤ 28 := by
  unfold encLinkAfterQuery
  split
  · change 0 ≤ 28; omega
  · have bound := encLinkControlState_cost (executeLinear encLinkFinish memory)
    change 20 + _ ≤ 28
    omega

/-- Every query body stays within the query and tail reserves. -/
theorem encLinkQuerySamples_cost [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (result : Memory × Nat × Fin 7468)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (supported : result ∈ (encLinkQuerySamples attempts count overlayCount memory).support) :
    result.2.1 ≤ internalForwardReserve attempts count overlayCount 28 memory := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have query := internalForwardSamples_cost attempts count overlayCount memory before spent
    attemptFits tableFits counter member
  have tail := encLinkAfterQuery_cost before
  change spent + (encLinkAfterQuery before).2.1 ≤ _
  unfold internalForwardReserve at query ⊢
  omega

/-- Every complete iteration stays within its exact reserve. -/
theorem encLinkIterationSamples_cost [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (index : EncPRF.PermutationIndex) (rest : List Bool) (result : Memory × Nat × Fin 7468)
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded (encLinkPrepared memory index rest)).registers 0 = BitVec.ofNat 256 count)
    (supported : result ∈ (encLinkIterationSamples attempts count overlayCount memory index rest).support) :
    result.2.1 ≤ encLinkIterationReserve attempts count overlayCount 0 memory index rest := by
  obtain ⟨before, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have bound := encLinkQuerySamples_cost attempts count overlayCount (encLinkPrepared memory index rest)
    before attemptFits tableFits counter member
  change 121 + before.2.1 ≤ 121 + internalForwardReserve attempts count overlayCount (28 + 0) _
  simpa only [Nat.add_zero] using Nat.add_le_add_left bound 121

/-- The complete iteration has a fixed polynomial instruction bound. -/
theorem encLinkIterationReserve_bound (attempts count overlayCount fuel : Nat)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) :
    encLinkIterationReserve attempts count overlayCount fuel memory index rest ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 274 + fuel := by
  have bound := internalForwardReserve_bound attempts count overlayCount (28 + fuel)
    (encLinkPrepared memory index rest)
  change 198 + 1 + _ ≤ _ at bound
  unfold encLinkIterationReserve
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
