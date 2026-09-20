import Proof.Privacy.Simulator.Arithmetic.EncLinkComplete

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- Every complete link sample retains a terminal label and fits its exact reserve. -/
theorem encLinkSamples_bounds [BN254.FieldCertificate]
    (attempts limit output : Nat) (memory : Memory) (state : SparseOracleFamily)
    (key : BN254.BaseField) (suffix : List Bool) (attemptFits : attempts < 2 ^ 256)
    (ready : ∀ hash ∈ (hashHandlerSamples state.hash.length (encLinkSaved memory)).support,
      EncLinkLoopMemory (encLinkStarted state key hash.1) (encLinkScheduled hash.1) encLinkIndices suffix
        (Security.SimulatorMachine.hashFin.symm (hash.1.registers 8).toFin).1 output limit)
    (result : EncLinkResult) (supported : result ∈ (encLinkSamples attempts memory state key suffix).support) :
    result.1.2.1 ≤ encLinkReserve attempts limit 0 memory state ∧
      (result.1.2.2 = 7466 ∨ result.1.2.2 = 7467) := by
  obtain ⟨hash, hashMember, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨tail, tailMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have initialized := ready hash hashMember
  have charged := encLinkLoopSamples_budget attempts _ suffix encLinkIndices (encLinkScheduled hash.1)
    (encLinkStarted state key hash.1) output limit initialized attemptFits tail tailMember
  have retained := encLinkLoopSamples_memory attempts _ suffix encLinkIndices (encLinkScheduled hash.1)
    (encLinkStarted state key hash.1) output limit initialized tail tailMember
  have hashBound := hashHandlerSamples_cost state.hash.length (encLinkSaved memory) hash.1 hash.2 hashMember
  rw [encLinkIndices_length] at charged
  constructor
  · change encLinkStartCost hash + tail.1.2.1 ≤ _
    unfold encLinkStartCost encLinkReserve
    omega
  · change tail.1.2.2 = 7466 ∨ tail.1.2.2 = 7467
    rcases retained.2.2 with failed | accepted
    · exact Or.inr failed
    · exact Or.inl accepted.1

end Kriterion.ArgoMAC.ArithmeticSimulator
