import Proof.Privacy.Simulator.Arithmetic.FreshQueryMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A fresh tail preserves every RAM cell outside its four possible insertion cells. -/
theorem freshQueryTail_other (count : Nat) (memory : Memory) (address : Word)
    (inputLeft : address ≠ memory.registers 1 - 2#256)
    (inputRight : address ≠ memory.registers 1 - 2#256 + 1#256)
    (outputLeft : address ≠ memory.registers 3 - 2#256)
    (outputRight : address ≠ memory.registers 3 - 2#256 + 1#256) :
    (freshQueryTail count memory).1.ram address = memory.ram address := by
  unfold freshQueryTail
  split
  · rfl
  · let scanned := (swapScan count (swapInitial (freshOutputInitial memory))).1
    have frame := freshOutputScan_frame count memory
    dsimp only at frame
    have r1 := frame.2 1 (by decide)
    have r3 := frame.2 3 (by decide)
    have untouched := installedFresh_other scanned address
      (by simpa only [scanned, r1] using inputLeft)
      (by simpa only [scanned, r1] using inputRight)
      (by simpa only [scanned, r3] using outputLeft)
      (by simpa only [scanned, r3] using outputRight)
    exact untouched.trans (congrFun frame.1 address)

/-- Every complete sparse-query sample preserves cells outside scratch and its insertion cells. -/
theorem permutationForwardSamples_other (attempts inputCount outputCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts inputCount outputCount memory).support)
    (address : Word) (outsideScratch : 8 ≤ address.toNat)
    (inputLeft : address ≠ memory.registers 1 - 2#256)
    (inputRight : address ≠ memory.registers 1 - 2#256 + 1#256)
    (outputLeft : address ≠ memory.registers 3 - 2#256)
    (outputRight : address ≠ memory.registers 3 - 2#256 + 1#256) :
    final.ram address = memory.ram address := by
  unfold permutationForwardSamples at supported
  dsimp only at supported
  split at supported
  · obtain ⟨⟨sampled, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have r1 := freshChoice_metadata attempts (knownQueryScan inputCount outputCount memory).1 sampled spent member (1 : Fin 6)
    have r3 := freshChoice_metadata attempts (knownQueryScan inputCount outputCount memory).1 sampled spent member (3 : Fin 6)
    have i1 := knownQueryScan_metadata inputCount outputCount memory 1 (by decide)
    have i3 := knownQueryScan_metadata inputCount outputCount memory 3 (by decide)
    have inputBase : (freshChoiceFinal sampled).registers 1 = memory.registers 1 := r1.trans i1
    have outputBase : (freshChoiceFinal sampled).registers 3 = memory.registers 3 := r3.trans i3
    rw [freshQueryTail_other outputCount (freshChoiceFinal sampled) address
      (by simpa only [inputBase] using inputLeft) (by simpa only [inputBase] using inputRight)
      (by simpa only [outputBase] using outputLeft) (by simpa only [outputBase] using outputRight),
      freshChoice_ram attempts (knownQueryScan inputCount outputCount memory).1 sampled spent member address outsideScratch,
      (knownQueryScan_data inputCount outputCount memory).1]
  · simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    exact congrFun (knownQueryScan_data inputCount outputCount memory).1 address

/-- The deterministic fresh tail leaves every bit stack unchanged. -/
theorem freshQueryTail_bits (count : Nat) (memory : Memory) :
    (freshQueryTail count memory).1.bits = memory.bits := by
  unfold freshQueryTail
  split
  · rfl
  · exact (swapScan_data count (swapInitial (freshOutputInitial memory))).1

/-- Every complete sparse-query sample leaves every bit stack unchanged. -/
theorem permutationForwardSamples_bits (attempts inputCount outputCount : Nat)
    (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts inputCount outputCount memory).support) :
    final.bits = memory.bits := by
  unfold permutationForwardSamples at supported
  dsimp only at supported
  split at supported
  · obtain ⟨⟨sampled, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    rw [freshQueryTail_bits,
      freshChoice_bits attempts (knownQueryScan inputCount outputCount memory).1 sampled spent member,
      (knownQueryScan_data inputCount outputCount memory).2]
  · simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    exact (knownQueryScan_data inputCount outputCount memory).2

end Kriterion.ArgoMAC.ArithmeticSimulator
