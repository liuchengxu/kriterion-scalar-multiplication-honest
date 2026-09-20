import Proof.Privacy.Simulator.Arithmetic.HistoryFreshCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The range tail converts the lookup flag to the freshness flag. -/
theorem historyFreshBlock_finish [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 43 → Fin (host.size + 1)) (present : ContainsHistoryFresh host labels)
    (memory : Memory) (fuel : Nat) :
    run host (fuel + 2) ⟨labels 39, memory⟩ =
      (run host fuel ⟨labels 41, {memory with registers := Function.update memory.registers 7 (memory.registers 12 ^^^ 1)}⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  have first : host.code[(labels 39).val] = .constant 7 1 (labels 40) := by
    simpa [historyFresh, relocate] using present 39 (by decide)
  have second : host.code[(labels 40).val] = .arithmetic .xor 7 12 7 (labels 41) := by
    simpa [historyFresh, relocate] using present 40 (by decide)
  simp [run, step, first, second, Arithmetic.eval, PMF.pure_bind, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc]

/-- The collision tail returns a zero freshness flag. -/
theorem historyFreshBlock_reject [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 43 → Fin (host.size + 1)) (present : ContainsHistoryFresh host labels)
    (memory : Memory) (fuel : Nat) :
    run host (fuel + 1) ⟨labels 42, memory⟩ =
      (run host fuel ⟨labels 41, {memory with registers := Function.update memory.registers 7 0}⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  have code : host.code[(labels 42).val] = .constant 7 0 (labels 41) := by
    simpa [historyFresh, relocate] using present 42 (by decide)
  simp [run, step, code, PMF.pure_bind]

/-- The selected tail returns the exact checked freshness result. -/
theorem historyFreshBlock_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 43 → Fin (host.size + 1)) (present : ContainsHistoryFresh host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((historyFreshTail count memory).2 + fuel) ⟨labels 18, memory⟩ =
      (run host fuel ⟨labels 41, (historyFreshTail count memory).1⟩).map
        (Option.map fun result => (result.1, result.2 + (historyFreshTail count memory).2)) := by
  have code : host.code[(labels 18).val] = .branch 12 (labels 19) (labels 42) := by
    simpa [historyFresh, relocate] using present 18 (by decide)
  by_cases fresh : memory.registers 12 = 0
  · have initialCounter : (historyRangeReady memory).registers 10 = BitVec.ofNat 256 count := by
      simp [historyRangeReady, counter]
    have loaded := linear_continue host historyRangeLoad (labels ∘ historyRangeLoadLabels)
      (historyFreshBlock_rangeLoad host labels present) memory
      ((historyRangeScan count memory).2 + 1 + (fuel + 2))
    have scanned := tableBlock_continue host (labels ∘ historyRangeLabels)
      (historyFreshBlock_range host labels present) count (historyRangeReady memory) fits initialCounter (fuel + 2)
    change run host (7 + ((historyRangeScan count memory).2 + 1 + (fuel + 2))) ⟨labels 19, memory⟩ = _ at loaded
    rw [historyRangeLoad_memory] at loaded
    change run host ((historyRangeScan count memory).2 + 1 + (fuel + 2)) ⟨labels 26, historyRangeReady memory⟩ = _ at scanned
    rw [historyFreshTail, if_pos fresh]
    dsimp only
    rw [show (historyRangeScan count memory).2 + 11 + fuel =
      (7 + ((historyRangeScan count memory).2 + 1 + (fuel + 2))) + 1 by omega, run]
    simp only [step, code, fresh, ↓reduceIte, PMF.pure_bind]
    rw [loaded]
    change ((run host _ ⟨labels 26, historyRangeReady memory⟩).map _).map _ = _
    rw [scanned]
    change (((run host (fuel + 2) ⟨labels 39, (historyRangeScan count memory).1⟩).map _).map _).map _ = _
    rw [historyFreshBlock_finish host labels present]
    simp [PMF.map_comp, Option.map_map, Function.comp_def, historyRangeScan, historyRangeLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    norm_num only [← Nat.add_assoc]
  · rw [historyFreshTail, if_neg fresh]
    dsimp only
    rw [show 2 + fuel = (fuel + 1) + 1 by omega, run]
    simp only [step, code, fresh, ↓reduceIte, PMF.pure_bind]
    rw [historyFreshBlock_reject host labels present]
    simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The full host block returns after its exact domain and range scan charge. -/
theorem historyFreshBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 43 → Fin (host.size + 1)) (present : ContainsHistoryFresh host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((historyFreshSource count memory).2 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 41, (historyFreshSource count memory).1⟩).map
        (Option.map fun result => (result.1, result.2 + (historyFreshSource count memory).2)) := by
  have initialCounter : (historyDomainReady memory).registers 10 = BitVec.ofNat 256 count := by
    simp [historyDomainReady, counter]
  have saved := historyDomainScan_data count memory
  have finalCounter : (historyDomainScan count memory).1.ram
      (historyHeader (historyDomainScan count memory).1) = BitVec.ofNat 256 count := by
    simp only [historyHeader, saved.1, saved.2.2]
    exact counter
  have loaded := linear_continue host historyDomainLoad (labels ∘ historyDomainLoadLabels)
    (historyFreshBlock_domainLoad host labels present) memory
    ((historyDomainScan count memory).2 + 1 + ((historyFreshTail count (historyDomainScan count memory).1).2 + fuel))
  have scanned := tableBlock_continue host (labels ∘ historyDomainLabels)
    (historyFreshBlock_domain host labels present) count (historyDomainReady memory) fits initialCounter
    ((historyFreshTail count (historyDomainScan count memory).1).2 + fuel)
  change run host (5 + ((historyDomainScan count memory).2 + 1 + _)) ⟨labels 0, memory⟩ = _ at loaded
  rw [historyDomainLoad_memory] at loaded
  change run host ((historyDomainScan count memory).2 + 1 + _) ⟨labels 5, historyDomainReady memory⟩ = _ at scanned
  rw [historyFreshSource_tail]
  dsimp only
  rw [show (historyDomainScan count memory).2 + 6 +
    (historyFreshTail count (historyDomainScan count memory).1).2 + fuel =
    5 + ((historyDomainScan count memory).2 + 1 +
      ((historyFreshTail count (historyDomainScan count memory).1).2 + fuel)) by omega, loaded]
  change (run host _ ⟨labels 5, historyDomainReady memory⟩).map _ = _
  rw [scanned]
  change ((run host _ ⟨labels 18, (historyDomainScan count memory).1⟩).map _).map _ = _
  rw [historyFreshBlock_tail host labels present count _ fits finalCounter]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, historyDomainScan, historyDomainLoad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  norm_num only [← Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
