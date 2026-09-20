import Proof.Privacy.Simulator.Arithmetic.InternalForwardBlock
import Proof.Privacy.Simulator.Arithmetic.ProgrammedForwardSource
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The internal source charges the stored query and its accepted overlay. -/
noncomputable def internalForwardSamples (attempts count overlayCount : Nat) (memory : Memory) : PMF (Memory × Nat) :=
  (storedForwardSamples attempts count memory).map fun result =>
    let tail := internalForwardTail overlayCount result.1
    (tail.1, result.2 - 1 + tail.2)

/-- The internal tail retains the complete RAM and all stacks. -/
theorem internalForwardTail_data (count : Nat) (memory : Memory) :
    (internalForwardTail count memory).1.ram = memory.ram ∧
    (internalForwardTail count memory).1.bits = memory.bits ∧
    (internalForwardTail count memory).1.registers 7 = memory.registers 7 := by
  unfold internalForwardTail
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨(overlayForward_data count memory).1,
      (overlayForward_data count memory).2.1, (overlayForward_data count memory).2.2 7 (by decide)⟩

/-- Every internal query preserves all bit stacks. -/
theorem internalForwardSamples_bits (attempts count overlayCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support) :
    final.bits = memory.bits := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (internalForwardTail_data overlayCount before).2.1.trans
    (storedForwardSamples_bits attempts count memory before spent member)

/-- The acceptance observer retains the exact programmed answer. -/
theorem internalForwardTail_value (count : Nat) (memory : Memory) :
    queryValue (internalForwardTail count memory).1 = overlayQueryValue count memory := by
  unfold queryValue
  rw [(internalForwardTail_data count memory).2.2]
  by_cases failed : memory.registers 7 = 0#256
  · simp [failed, overlayQueryValue]
  · simp [failed, overlayQueryValue, internalForwardTail]

/-- The internal query has the exact operational cutoff law. -/
theorem internalForwardSamples_wordReply [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (internalForwardSamples attempts state.base.used state.overlay.length memory).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  simp only [internalForwardSamples, PMF.map_comp, Function.comp_def, internalForwardTail_value]
  exact programmedForwardSamples_wordReply attempts memory oracle state input represented index operand fits overlayFits

/-- The complete internal reserve has a concrete linear instruction bound. -/
theorem internalForwardReserve_bound (attempts count overlayCount fuel : Nat) (memory : Memory) :
    (internalForward attempts).size + 1 + internalForwardReserve attempts count overlayCount fuel memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 324 + fuel := by
  have bound := storedForward_budget attempts count memory
  change 178 + 1 + 22 + _ ≤ _ at bound
  change 198 + 1 + _ ≤ _
  dsimp [internalForwardReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
