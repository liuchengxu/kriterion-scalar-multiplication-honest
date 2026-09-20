import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBudgeted

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source reads the history count from the same header as the fixed machine. -/
def checkedSlotHistoryCount (memory : Memory) : Nat :=
  ((executeLinear checkedSlotStart memory).ram (historyHeader (executeLinear checkedSlotStart memory))).toNat

/-- The source reads the used count after the deterministic freshness prefix. -/
def checkedSlotUsedCount (memory : Memory) : Nat :=
  ((oracleLoaded (checkedSlotRestored (checkedSlotPrepared (checkedSlotHistoryCount memory) memory))).registers 0).toNat

/-- The source reads the current override count for the selected public oracle. -/
def checkedSlotOverlayCount (memory : Memory) : Nat :=
  let loaded := oracleLoaded (checkedSlotRestored (checkedSlotPrepared (checkedSlotHistoryCount memory) memory))
  (loaded.ram (overlayHeader loaded)).toNat

/-- The private query retains the selected override count. -/
def CheckedSlotCoherent (attempts : Nat) (memory : Memory) : Prop :=
  ∀ result ∈ (storedForwardSamples attempts (checkedSlotUsedCount memory)
    (checkedSlotRestored (checkedSlotPrepared (checkedSlotHistoryCount memory) memory))).support,
    result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 (checkedSlotOverlayCount memory)

/-- The caller bounds every stored count used by one checked command. -/
def CheckedSlotReady (attempts limit : Nat) (memory : Memory) : Prop :=
  CheckedSlotCoherent attempts memory ∧ checkedSlotUsedCount memory ≤ limit ∧
    checkedSlotOverlayCount memory ≤ limit ∧ checkedSlotHistoryCount memory ≤ limit

/-- The automatic source uses the exact RAM counts of the compiled machine. -/
noncomputable def checkedSlotAutomaticSamples (attempts : Nat) (memory : Memory) : PMF (Fin 305 × Memory × Nat) :=
  checkedSlotSamples attempts (checkedSlotUsedCount memory) (checkedSlotOverlayCount memory)
    (checkedSlotHistoryCount memory) memory

/-- The checked host block uses a fixed reserve once the caller bounds its table counts. -/
theorem checkedSlotBlock_automatic [BN254.FieldCertificate] (host : Machine)
    (attempts limit fuel : Nat) (labels : Fin 305 → Fin (host.size + 1))
    (present : ContainsCheckedSlot host attempts labels) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : CheckedSlotReady attempts limit memory) :
    run host (checkedSlotRunBudget attempts limit + fuel) ⟨labels 0, memory⟩ =
      (checkedSlotAutomaticSamples attempts memory).bind fun result =>
        (run host (checkedSlotRunBudget attempts limit + fuel - result.2.2)
          ⟨labels result.1, result.2.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2.2)) := by
  apply checkedSlotBlock_budgeted host attempts (checkedSlotUsedCount memory) (checkedSlotOverlayCount memory)
    (checkedSlotHistoryCount memory) (checkedSlotRunBudget attempts limit + fuel) labels present memory attemptFits
  · exact BitVec.isLt _
  · exact BitVec.isLt _
  · exact BitVec.isLt _
  · simp only [checkedSlotHistoryCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [checkedSlotUsedCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact ready.1
  · exact le_trans (checkedSlotReserve_uniform attempts (checkedSlotUsedCount memory)
      (checkedSlotOverlayCount memory) (checkedSlotHistoryCount memory) limit memory
      ready.2.1 ready.2.2.1 ready.2.2.2) (Nat.le_add_right _ _)

end Kriterion.ArgoMAC.ArithmeticSimulator
