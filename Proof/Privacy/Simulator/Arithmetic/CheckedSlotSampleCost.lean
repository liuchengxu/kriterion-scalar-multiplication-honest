import Proof.Privacy.Simulator.Arithmetic.CheckedSlotAutomatic

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every checked sample has a valid return label and fits its reserve. -/
theorem checkedSlotSamples_cost [BN254.FieldCertificate]
    (attempts count overlayCount historyCount : Nat) (memory : Memory)
    (result : Fin 305 × Memory × Nat)
    (attemptFits : attempts < 2 ^ 256) (countFits : count < 2 ^ 256)
    (counter : (oracleLoaded (checkedSlotRestored (checkedSlotPrepared historyCount memory))).registers 0 =
      BitVec.ofNat 256 count)
    (supported : result ∈ (checkedSlotSamples attempts count overlayCount historyCount memory).support) :
    result.2.2 ≤ checkedSlotReserve attempts count overlayCount historyCount 0 memory ∧
      (result.1 = 300 ∨ result.1 = 304) := by
  obtain ⟨branch, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  change branch ∈ (checkedSlotBranchSamples attempts count overlayCount (checkedSlotPrepared historyCount memory)).support at member
  by_cases collision : (checkedSlotPrepared historyCount memory).registers 7 = 0
  · simp only [checkedSlotBranchSamples, if_pos collision] at member
    have same : branch = (300, executeLinear checkedSlotCollision (checkedSlotPrepared historyCount memory), 4) := by
      simpa only [PMF.support_pure, Set.mem_singleton_iff] using member
    subst branch
    simp [checkedSlotReserve, checkedSlotBranchReserve, collision]
  · simp only [checkedSlotBranchSamples, if_neg collision] at member
    obtain ⟨draw, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have bound := checkedSlotForward_enough attempts count overlayCount 0
      (checkedSlotRestored (checkedSlotPrepared historyCount memory)) draw.1 draw.2
      attemptFits countFits counter drawn
    simp only [checkedSlotReserve, checkedSlotBranchReserve, if_neg collision]
    constructor
    · unfold checkedSlotForwardCost
      split <;> omega
    · unfold checkedSlotForwardReturn
      split <;> simp

/-- Every automatic sample fits the common table-length reserve. -/
theorem checkedSlotAutomaticSamples_cost [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (result : Fin 305 × Memory × Nat) (attemptFits : attempts < 2 ^ 256)
    (ready : CheckedSlotReady attempts limit memory)
    (supported : result ∈ (checkedSlotAutomaticSamples attempts memory).support) :
    result.2.2 ≤ checkedSlotRunBudget attempts limit ∧ (result.1 = 300 ∨ result.1 = 304) := by
  have counted : (oracleLoaded (checkedSlotRestored (checkedSlotPrepared (checkedSlotHistoryCount memory) memory))).registers 0 =
      BitVec.ofNat 256 (checkedSlotUsedCount memory) := by
    simp only [checkedSlotUsedCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have bound := checkedSlotSamples_cost attempts (checkedSlotUsedCount memory) (checkedSlotOverlayCount memory)
    (checkedSlotHistoryCount memory) memory result attemptFits (BitVec.isLt _) counted supported
  exact ⟨le_trans bound.1 (checkedSlotReserve_uniform attempts (checkedSlotUsedCount memory)
    (checkedSlotOverlayCount memory) (checkedSlotHistoryCount memory) limit memory
    ready.2.1 ready.2.2.1 ready.2.2.2), bound.2⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
