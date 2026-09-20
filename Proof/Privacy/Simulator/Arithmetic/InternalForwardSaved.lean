import Proof.Privacy.Simulator.Arithmetic.InternalForwardGrowth
import Proof.Privacy.Simulator.Arithmetic.OracleHistoryFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- A stored query preserves private words above its metadata scratch cells. -/
theorem storedForwardSamples_private (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support)
    (oracle : Fin 15749) (cell : Nat) (lower : 14 ≤ cell) (privateBound : cell < 2 ^ 96)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have inputBase := oracleLoaded_inputBase memory oracle count index counter (by omega)
  have outputBase := oracleLoaded_outputBase memory oracle count index counter (by omega)
  have kept := permutationForwardSamples_private attempts count (oracleLoaded memory) before spent member
    oracle cell (by omega) privateBound inputBase outputBase fits
  have saved := permutationForwardSamples_private attempts count (oracleLoaded memory) before spent member
    oracle 13 (by decide) (by decide) inputBase outputBase fits
  have header : before.ram 13 = oracleAddress oracle 0 0 :=
    saved.trans ((oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address]))
  change Function.update before.ram (before.ram 13) (before.registers 0) (BitVec.ofNat 256 cell) = _
  rw [header, Function.update_of_ne (Ne.symm (oracleAddress_private_disjoint oracle 0 0 cell (by decide) privateBound)), kept]
  have apart (scratch : Nat) (small : scratch < 14) : BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch := by
    intro same
    have values := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans privateBound (by decide : 2 ^ 96 < 2 ^ 256)),
      Nat.mod_eq_of_lt (show scratch < 2 ^ 256 by omega)] at values
    omega
  change oracleLoadRam memory (BitVec.ofNat 256 cell) = _
  have apart9 : BitVec.ofNat 256 cell ≠ (9 : Word) := apart 9 (by decide)
  have apart12 : BitVec.ofNat 256 cell ≠ (12 : Word) := apart 12 (by decide)
  have apart13 : BitVec.ofNat 256 cell ≠ (13 : Word) := apart 13 (by decide)
  simp only [oracleLoadRam, Function.update_of_ne apart9, Function.update_of_ne apart12, Function.update_of_ne apart13]

/-- An internal query preserves private words above its metadata scratch cells. -/
theorem internalForwardSamples_private (attempts count overlayCount : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support)
    (oracle : Fin 15749) (cell : Nat) (lower : 14 ≤ cell) (privateBound : cell < 2 ^ 96)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [(internalForwardTail_data overlayCount before).1]
  exact storedForwardSamples_private attempts count memory before spent member oracle cell lower privateBound index counter fits

/-- An internal query retains the canonical selected header. -/
theorem internalForwardSamples_header (attempts count overlayCount : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (internalForwardSamples attempts count overlayCount memory).support)
    (oracle : Fin 15749) (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (counter : memory.ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 count)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) : final.registers 6 = oracleAddress oracle 0 0 := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have kept := (storedForwardSamples_historyFrame attempts count memory before spent member oracle index counter fits).1
  unfold internalForwardTail
  split
  · exact kept
  · exact ((overlayForward_data overlayCount before).2.2 6 (by decide)).trans kept

/-- Every accepted internal reply has a canonical finite block encoding. -/
theorem internalForwardSamples_valueWitness [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈ (internalForwardSamples attempts state.base.used state.overlay.length memory).support)
    (accepted : final.registers 7 ≠ 0#256) :
    ∃ value : Fin (2 ^ 128), final.registers 8 = BitVec.ofNat 256 value.val := by
  have source : (internalForwardSamples attempts state.base.used state.overlay.length memory).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.forward input)).map (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
    simpa only [internalForwardSamples, PMF.map_comp, Function.comp_def, internalForwardTail_value] using
      programmedForwardSamples_wordReply attempts memory oracle state input represented index operand fits overlayFits
  have reached : some (final.registers 8) ∈
      ((internalForwardSamples attempts state.base.used state.overlay.length memory).map (fun result => queryValue result.1)).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨(final, cost), supported, by simp [queryValue, accepted]⟩
  rw [source] at reached
  obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases value with
  | none => simp at same
  | some value => exact ⟨value.1, (Option.some.inj same).symm⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
