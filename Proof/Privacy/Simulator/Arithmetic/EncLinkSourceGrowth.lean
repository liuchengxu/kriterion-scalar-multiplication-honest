import Proof.Privacy.Simulator.Arithmetic.SharedCommandGrowth
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedCutoff
import Proof.Privacy.Simulator.Arithmetic.EncLinkProgramRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- Each link read adds at most one base pair and retains the hash table. -/
theorem oracleFamilyForward_growth (attempts limit : Nat) (state next : SparseOracleFamily)
    (oracle : Fin 15748) (input reply : Fin (2 ^ 128))
    (base : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlay : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (member : some (reply, next) ∈ (oracleFamilyCutoff attempts (.inl (oracle, .forward input)) state).support) :
    (∀ index, (next.permutations index).base.used ≤ limit + 1) ∧
    (∀ index, (next.permutations index).overlay.length ≤ limit + 1) ∧ next.hash = state.hash := by
  rw [oracleFamilyCutoff_forward] at member
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  cases raw with
  | none => simp at same
  | some raw =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨_, rfl⟩ := same
    have exactMember := drawCutoffLaw_supported attempts _ raw reached
    have growth := (state.permutations oracle).forward_resources input raw exactMember
    have counts := publicReadFamily_counts state oracle raw.2 limit base overlay growth.1 growth.2
    exact ⟨counts.1, counts.2, rfl⟩

/-- The selected-row source has one read per row and no hash calls. -/
theorem encLinkRowsProgram_growth (attempts limit : Nat) (state next : SparseOracleFamily)
    (firstKey secondKey : Block) (x y : BitVec coordinateBitCount) (labels : Fin 508 → Block)
    (positions : List (Fin 508)) (values : List Block)
    (base : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlay : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (member : some (values, next) ∈ ((encLinkRowsProgram firstKey secondKey x y labels positions).cutoffLaw
      (oracleFamilyCutoff attempts) state).support) :
    (∀ index, (next.permutations index).base.used ≤ limit + positions.length) ∧
    (∀ index, (next.permutations index).overlay.length ≤ limit + positions.length) ∧ next.hash = state.hash := by
  induction positions generalizing limit state values with
  | nil =>
    simp only [encLinkRowsProgram, SimulatorMachine.Program.cutoffLaw, PMF.mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at member
    obtain ⟨rfl, rfl⟩ := member
    exact ⟨base, overlay, rfl⟩
  | cons position positions ih =>
    simp only [encLinkRowsProgram, SimulatorMachine.Program.cutoffLaw] at member
    obtain ⟨head, reached, tail⟩ := (mem_support_bindCutoff _ _ _).mp member
    have grown := oracleFamilyForward_growth attempts limit state head.2 _ _ head.1 base overlay reached
    obtain ⟨raw, accepted, same⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
    cases raw with
    | none => simp at same
    | some raw =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
      have sameState := same.2
      subst next
      have final := ih (limit + 1) head.2 raw.1 grown.1 grown.2.1 accepted
      refine ⟨?_, ?_, final.2.2.trans grown.2.2⟩
      · intro index
        have := final.1 index
        simp only [List.length_cons]
        omega
      · intro index
        have := final.2.1 index
        simp only [List.length_cons]
        omega

end
/-- The hash source leaves every permutation unchanged and adds at most one hash entry. -/
theorem oracleFamilyHash_growth (state next : SparseOracleFamily) (key : BaseField) (reply : Fin (2 ^ 256))
    (member : (reply, next) ∈ (oracleFamilySampled (.inr key) state).support) :
    next.permutations = state.permutations ∧ next.hash.length ≤ state.hash.length + 1 := by
  simp only [oracleFamilySampled, oracleFamilyDraw, Draw.map_distribution] at member
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  cases same
  rw [← hashSource_recover state.hash key] at reached
  obtain ⟨observed, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases same
  refine ⟨rfl, ?_⟩
  change (hashNextTable state.hash key observed.1).length ≤ state.hash.length + 1
  unfold hashNextTable
  split <;> simp

/-- The complete link source adds at most 508 permutation pairs and one hash entry. -/
theorem encLinkProgram_growth (attempts limit : Nat) (state next : SparseOracleFamily)
    (curve : CurveGateRequest) (input : AffineInput) (mac linked : InputMac)
    (base : ∀ index, (state.permutations index).base.used ≤ limit)
    (overlay : ∀ index, (state.permutations index).overlay.length ≤ limit)
    (member : some (linked, next) ∈ ((encLinkProgram curve input mac).cutoffLaw
      (oracleFamilyCutoff attempts) state).support) :
    (∀ index, (next.permutations index).base.used ≤ limit + 508) ∧
    (∀ index, (next.permutations index).overlay.length ≤ limit + 508) ∧
      next.hash.length ≤ state.hash.length + 1 := by
  have mapped : some (encLinkMacWords linked, next) ∈ (((encLinkProgram curve input mac).cutoffLaw
      (oracleFamilyCutoff attempts) state).map (Option.map fun result => (encLinkMacWords result.1, result.2))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨some (linked, next), member, rfl⟩
  rw [encLinkProgram_rows] at mapped
  obtain ⟨hash, hashMember, rowsMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp mapped
  have hashGrowth := oracleFamilyHash_growth state hash.2 (curve.result input) hash.1 hashMember
  have rows := encLinkRowsProgram_growth attempts limit hash.2 next _ _ _ _ _ _ _
    (by simpa only [hashGrowth.1] using base) (by simpa only [hashGrowth.1] using overlay) rowsMember
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.length_finRange] using rows.1
  · simpa only [List.length_finRange] using rows.2.1
  · rw [rows.2.2]
    exact hashGrowth.2

/-- The shared internal link retains history and has the same exact source growth bound. -/
theorem sharedLinkProgram_growth (attempts limit : Nat) (state next : SharedOracleSource)
    (curve : CurveGateRequest) (input : AffineInput) (mac linked : InputMac)
    (bounded : SharedSourceCounts state limit)
    (member : some (linked, next) ∈ (runSampledCutoff (sharedSourceCutoff attempts)
      (sharedCombinedProgram (SimulatorMachine.link curve input mac)).toOracle state).support) :
    SharedSourceCounts next (limit + 508) ∧ next.family.hash.length ≤ state.family.hash.length + 1 := by
  rw [← encLinkProgram_sharedCutoff attempts curve input mac state.family state.metadata] at member
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  cases raw with
  | none => simp at same
  | some raw =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    rw [SimulatorMachine.Program.cutoffLaw_toOracle] at reached
    have growth := encLinkProgram_growth attempts limit state.family raw.2 curve input mac raw.1
      bounded.1 bounded.2.1 reached
    exact ⟨⟨growth.1, growth.2.1, fun index => (bounded.2.2 index).trans (Nat.le_add_right _ _)⟩, growth.2.2⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
