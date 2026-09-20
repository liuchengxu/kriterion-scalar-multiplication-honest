import Proof.Privacy.Simulator.Arithmetic.GateLoopJointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- Each accepted actual slot has a source witness in the exact joint law. -/
theorem gateSlotJoint_witness (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory (commands slot))
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (gateDriverSlotSamples attempts gate slot memory).support) (accepted : result.1 ≠ 304) :
    ∃ next, some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state (commands slot)).support := by
  have projected : some ((), result) ∈ ((gateDriverSlotSamples attempts gate slot memory).map
      (fun result => if result.1 = 304 then none else some ((), result))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, by simp only [if_neg accepted]⟩
  rw [← gateDriverSlotCoupledSamples_machine attempts gate slot memory state (commands slot)
    represented.family represented.capacity represented.history stored.index stored.operand stored.target
    (represented.historyFits room)] at projected
  obtain ⟨joint, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  cases joint with
  | none => simp at equal
  | some joint =>
      obtain ⟨value, actual, next⟩ := joint
      cases value
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
      subst result
      exact ⟨next, member⟩

/-- The source relation supplies the saved test's complete readiness condition. -/
theorem gateTestReady_of_source (attempts limit cap : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : memory.ram 20 = 3 → GateCommandMemory gate 2 memory (commands 2))
    (bounded : limit ≤ cap) (room : 256 + 2 * (cap + 1) < 2 ^ 110) :
    GateTestReady attempts cap gate memory := by
  intro selected
  have count : memory.ram 20 = 3 := by
    change memory.ram 20 ^^^ 3 = 0 at selected
    exact BitVec.xor_eq_zero_iff.mp selected
  exact gateDriverSlotReady_of_source attempts cap gate 2 _ state (commands 2)
    ((represented.mono bounded).ramEq rfl) ((stored count).ramEq rfl) room

/-- The source relation supplies both remaining slot reserves. -/
theorem gateSecondReady_of_source [BN254.FieldCertificate] (attempts limit cap : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (stored : ∀ slot, slot.val < 2 ∨ memory.ram 20 = 3 → GateCommandMemory gate slot memory (commands slot))
    (bounded : limit + 1 ≤ cap) (room : 256 + 2 * (cap + 1) < 2 ^ 110) :
    GateSecondReady attempts cap gate memory := by
  refine ⟨gateDriverSlotReady_of_source attempts cap gate 1 memory state (commands 1)
    (represented.mono (by omega)) (stored 1 (Or.inl (by decide))) room, ?_⟩
  intro result supported normal
  obtain ⟨next, member⟩ := gateSlotJoint_witness attempts limit gate 1 commands memory state represented
    (stored 1 (Or.inl (by decide))) (by omega) result supported (by rw [normal]; decide)
  apply gateTestReady_of_source attempts (limit + 1) cap gate commands result.2.1 next
    (gateDriverSlotCoupledSamples_memory attempts limit gate 1 memory state (commands 1) represented
      (stored 1 (Or.inl (by decide))) (by omega) result next member)
  · intro count
    exact GateCommandMemory.activeAfterSlot attempts limit gate 1 memory state commands represented
      (stored 1 (Or.inl (by decide))) stored (by omega) result next member 2 (Or.inr count)
  · exact bounded
  · exact room

/-- The source relation supplies the complete gate's actual count and coherence reserves. -/
theorem gateDriverReady_of_source [BN254.FieldCertificate] (attempts limit cap : Nat) (gate : GateCode)
    (commands : Fin 3 → SharedCommand) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (bounded : limit + 2 ≤ cap) (room : 256 + 2 * (cap + 1) < 2 ^ 110) :
    GateDriverReady attempts cap gate memory := by
  refine ⟨gateDriverSlotReady_of_source attempts cap gate 0 _ state (commands 0)
    (represented.mono (by omega)) (stored 0 (Or.inl (by decide))) room, ?_⟩
  intro result supported normal
  obtain ⟨next, member⟩ := gateSlotJoint_witness attempts limit gate 0 commands _ state represented
    (stored 0 (Or.inl (by decide))) (by omega) result supported (by rw [normal]; decide)
  exact gateSecondReady_of_source attempts (limit + 1) cap gate commands result.2.1 next
    (gateDriverSlotCoupledSamples_memory attempts limit gate 0 _ state (commands 0) represented
      (stored 0 (Or.inl (by decide))) (by omega) result next member)
    (GateCommandMemory.activeAfterSlot attempts limit gate 0 _ state commands represented
      (stored 0 (Or.inl (by decide))) stored (by omega) result next member) (by omega) room

/-- The coupled readiness condition supplies one actual reserve for the complete loop. -/
theorem gateLoopReady_of_coupled [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit cap : Nat) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady plan commands third attempts remaining index limit memory state)
    (bounded : limit + 3 * remaining ≤ cap) (room : 256 + 2 * (cap + 1) < 2 ^ 110)
    (attemptFits : attempts < 2 ^ 256) : GateLoopReady plan attempts cap remaining index memory := by
  induction remaining generalizing index limit memory state with
  | zero => trivial
  | succ remaining ih =>
      by_cases inside : index < count
      · simp only [GateLoopCoupledReady, dif_pos inside] at ready
        simp only [GateLoopReady, dif_pos inside]
        refine ⟨gateDriverReady_of_source attempts limit cap plan[index] (commands ⟨index, inside⟩)
          memory state ready.1 ready.2.1 (by omega) room, ?_⟩
        intro result supported normal
        have projected : some result ∈ ((gateDriverSamples attempts plan[index] memory).map
            (fun result => if result.1 = 1035 then none else some result)).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, by simp only [normal, show (1034 : Fin 1036) ≠ 1035 by decide, ↓reduceIte]⟩
        rw [← gateDriverCoupled_machine attempts limit plan[index] (commands ⟨index, inside⟩)
          memory state ready.1 ready.2.1 (by omega) attemptFits] at projected
        obtain ⟨joint, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
        cases joint with
        | none => simp at equal
        | some joint =>
            obtain ⟨actual, next⟩ := joint
            simp only [Option.map_some, Option.some.injEq] at equal
            subst result
            exact ih (index + 1) (limit + 3) actual.2.1 next (ready.2.2.2 _ member) (by omega)
      · simp only [GateLoopCoupledReady, dif_neg inside] at ready

end
end Kriterion.ArgoMAC.ArithmeticSimulator
