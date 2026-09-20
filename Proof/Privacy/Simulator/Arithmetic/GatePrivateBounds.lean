import Proof.Privacy.Simulator.Arithmetic.GateTypedData
import Proof.Privacy.Simulator.Arithmetic.GateSchedule
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineSetup

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each bounded offset has its exact private address without word wraparound. -/
theorem privateAddress_bounds (base offset count : Nat) (lower : 32 ≤ base)
    (upper : base + count ≤ 2 ^ 96) (inside : offset < count) :
    32 ≤ (BitVec.ofNat 256 base + BitVec.ofNat 256 offset).toNat ∧
    (BitVec.ofNat 256 base + BitVec.ofNat 256 offset).toNat < 2 ^ 96 := by
  have wordFits : base + offset < 2 ^ 256 := by
    have sizes : 2 ^ 96 < (2 ^ 256 : Nat) := by decide
    omega
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordFits]
  omega

/-- The complete source, input record, and selected-label buffer lie in private RAM. -/
theorem GatePrivateAddresses.of_bounds (memory : Memory) (gate : GateCode) (labelBase : Nat)
    (sourcePointer : memory.registers 11 = BitVec.ofNat 256 privateBase)
    (inputPointer : memory.registers 12 = BitVec.ofNat 256 onlineInputBase)
    (labelPointer : memory.registers 14 = BitVec.ofNat 256 labelBase)
    (labelLower : 32 ≤ labelBase) (labelUpper : labelBase + 508 ≤ 2 ^ 96)
    (sourceOffsets : ∀ offset ∈ [gate.target, gate.quotient, gate.table], offset < 838208) :
    GatePrivateAddresses memory gate := by
  refine ⟨?_, ?_, ?_⟩
  · intro offset member
    rw [sourcePointer]
    exact privateAddress_bounds privateBase offset 838208 (by decide) (by decide) (sourceOffsets offset member)
  · rw [inputPointer]
    apply privateAddress_bounds onlineInputBase (selectedCoordinate gate.selected) 2 (by decide) (by decide)
    unfold selectedCoordinate
    split <;> omega
  · rw [labelPointer]
    exact privateAddress_bounds labelBase gate.selected.val 508 labelLower labelUpper gate.selected.isLt

/-- Every curve descriptor reads only the private source and label buffers. -/
theorem curveGateCode_private (memory : Memory) (gate : Fin 5) (bit : Fin 254) (labelBase : Nat)
    (sourcePointer : memory.registers 11 = BitVec.ofNat 256 privateBase)
    (inputPointer : memory.registers 12 = BitVec.ofNat 256 onlineInputBase)
    (labelPointer : memory.registers 14 = BitVec.ofNat 256 labelBase)
    (labelLower : 32 ≤ labelBase) (labelUpper : labelBase + 508 ≤ 2 ^ 96) :
    GatePrivateAddresses memory (curveGateCode gate bit) := by
  apply GatePrivateAddresses.of_bounds memory (curveGateCode gate bit) labelBase sourcePointer inputPointer labelPointer labelLower labelUpper
  intro offset member
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  simp only [curveGateCode, gateCodeAt, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with first | second | third <;> subst offset <;> omega

/-- Every point descriptor reads only the private source and label buffers. -/
theorem pointGateCode_private (memory : Memory) (row : Fin FieldMacToECMac.outputMacCount) (gate : Fin 12) (bit : Fin 254) (labelBase : Nat)
    (sourcePointer : memory.registers 11 = BitVec.ofNat 256 privateBase)
    (inputPointer : memory.registers 12 = BitVec.ofNat 256 onlineInputBase)
    (labelPointer : memory.registers 14 = BitVec.ofNat 256 labelBase)
    (labelLower : 32 ≤ labelBase) (labelUpper : labelBase + 508 ≤ 2 ^ 96) :
    GatePrivateAddresses memory (pointGateCode row gate bit) := by
  apply GatePrivateAddresses.of_bounds memory (pointGateCode row gate bit) labelBase sourcePointer inputPointer labelPointer labelLower labelUpper
  intro offset member
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have rowBound := row.isLt
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  unfold pointGateCode at member
  split at member
  · simp only [gateCodeAt, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third <;> subst offset <;> omega
  · split at member
    · simp only [gateCodeAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with first | second | third <;> subst offset <;> omega
    · simp only [gateCodeAt, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with first | second | third <;> subst offset <;> omega

end Kriterion.ArgoMAC.ArithmeticSimulator
