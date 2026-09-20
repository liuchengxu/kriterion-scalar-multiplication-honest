import Proof.Privacy.Simulator.Arithmetic.HashHandlerCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The hash source scans the loaded sparse table. -/
def hashScan (count : Nat) (memory : Memory) : Memory × Nat :=
  tableScan count (tableInitial (hashReady (oracleLoaded memory)))

/-- The loader, setup, and lookup preserve the exact scan prefix. -/
theorem hashHandler_start [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    runPrefix hashHandler ((hashScan count memory).2 + 27) ⟨0, memory⟩ =
      PMF.pure (some (false, ⟨35, (hashScan count memory).1⟩, (hashScan count memory).2 + 27)) := by
  rw [show (hashScan count memory).2 + 27 = 22 + (4 + ((hashScan count memory).2 + 1)) by omega,
    prefix_add]
  have loaded := linear_prefix hashHandler oracleLoad hashLoadLabels hashHandler_load memory
  change runPrefix hashHandler 22 ⟨0, memory⟩ = _ at loaded
  rw [loaded, PMF.pure_bind]
  change (runPrefix hashHandler (4 + ((hashScan count memory).2 + 1))
    ⟨22, executeLinear oracleLoad memory⟩).map _ = _
  rw [oracleLoad_memory, prefix_add]
  have ready := linear_prefix hashHandler hashSetup hashSetupLabels hashHandler_setup (oracleLoaded memory)
  change runPrefix hashHandler 4 ⟨22, oracleLoaded memory⟩ = _ at ready
  rw [ready, PMF.pure_bind]
  change ((runPrefix hashHandler ((hashScan count memory).2 + 1)
    ⟨26, executeLinear hashSetup (oracleLoaded memory)⟩).map _).map _ = _
  rw [hashSetup_memory]
  have scanned := tableBlock_prefix hashHandler hashTableLabels hashHandler_table count
    (hashReady (oracleLoaded memory)) fits (by simp [hashReady, counter])
  change runPrefix hashHandler ((hashScan count memory).2 + 1) ⟨26, hashReady (oracleLoaded memory)⟩ = _ at scanned
  rw [scanned, PMF.pure_map, PMF.pure_map]
  simp [hashTableLabels, hashScan, show hashSetup.length = 4 from rfl,
    show oracleLoad.length = 22 from rfl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rfl

/-- The count commit and final return take four instructions. -/
theorem hashHandler_finish [BN254.FieldCertificate] (extra : Nat) (memory : Memory) :
    run hashHandler (4 + extra) ⟨70, memory⟩ =
      PMF.pure (some (⟨73, oracleCommitted memory⟩, 4)) := by
  rw [show 4 + extra = 3 + (extra + 1) by omega]
  have committed := oracleCommit_continue hashHandler hashCommitLabels hashHandler_commit memory (extra + 1)
  change run hashHandler (3 + (extra + 1)) ⟨70, memory⟩ = _ at committed
  rw [committed]
  change (run hashHandler (extra + 1) ⟨73, oracleCommitted memory⟩).map _ = _
  simp [run, step, hashHandler, PMF.pure_map]

/-- The branch selects an exact fresh draw or a stored reply in one instruction. -/
theorem hashHandler_branch [BN254.FieldCertificate] (fuel : Nat) (memory : Memory) :
    run hashHandler (fuel + 1) ⟨35, memory⟩ =
      (run hashHandler fuel ⟨if memory.registers 12 = 0#256 then 39 else 67, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  simp [run, step, hashHandler]
  rfl

/-- A known reply retains its stored value and uses eight final instructions. -/
theorem hashHandler_found [BN254.FieldCertificate] (extra : Nat) (memory : Memory)
    (found : memory.registers 12 ≠ 0#256) :
    run hashHandler (8 + extra) ⟨35, memory⟩ =
      PMF.pure (some (⟨73, oracleCommitted (hashFound memory)⟩, 8)) := by
  rw [show 8 + extra = (3 + (4 + extra)) + 1 by omega, hashHandler_branch]
  simp only [if_neg found]
  have known := linear_continue hashHandler hashKnown hashKnownLabels hashHandler_known memory (4 + extra)
  change run hashHandler (3 + (4 + extra)) ⟨67, memory⟩ = _ at known
  rw [known, hashKnown_memory]
  change ((run hashHandler (4 + extra) ⟨70, hashFound memory⟩).map _).map _ = _
  rw [hashHandler_finish, PMF.pure_map, PMF.pure_map]
  rfl

/-- A fresh reply uses 256 fair bits and installs one key-value pair. -/
theorem hashHandler_fresh [BN254.FieldCertificate] (memory : Memory)
    (fresh : memory.registers 12 = 0#256) :
    run hashHandler 1818 ⟨35, memory⟩ =
      (coinFold 256 0).map fun value =>
        some (⟨73, oracleCommitted (hashInstalled (frame memory value 0 0))⟩, 1818) := by
  rw [show 1818 = (1797 + 20) + 1 from rfl, hashHandler_branch]
  simp only [if_pos fresh]
  rw [run_after_prefix]
  have sampled := wordBlock_prefix hashHandler 256 hashWordLabels hashHandler_word memory (by decide)
  change runPrefix hashHandler 1797 ⟨39, memory⟩ = _ at sampled
  rw [sampled, PMF.bind_map, PMF.map_bind]
  change (coinFold 256 0).bind _ = (coinFold 256 0).bind _
  congr 1
  funext value
  have installed := linear_continue hashHandler hashInstall hashInstallLabels hashHandler_install
    (frame memory value 0 0) 4
  change run hashHandler 20 ⟨51, frame memory value 0 0⟩ = _ at installed
  change ((run hashHandler 20 ⟨51, frame memory value 0 0⟩).map _).map _ = _
  rw [installed, hashInstall_memory]
  change (((run hashHandler 4 ⟨70, hashInstalled (frame memory value 0 0)⟩).map _).map _).map _ = _
  rw [show 4 = 4 + 0 from rfl, hashHandler_finish, PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

/-- The tail source records its complete state and its actual instruction charge. -/
noncomputable def hashTailSamples (memory : Memory) : PMF (Memory × Nat) :=
  if memory.registers 12 = 0#256 then
    (coinFold 256 0).map fun value => (oracleCommitted (hashInstalled (frame memory value 0 0)), 1818)
  else PMF.pure (oracleCommitted (hashFound memory), 8)

/-- Both hash paths fit the same finite tail budget. -/
theorem hashHandler_tail [BN254.FieldCertificate] (memory : Memory) :
    run hashHandler 1818 ⟨35, memory⟩ = (hashTailSamples memory).map
      (fun result => some (⟨73, result.1⟩, result.2)) := by
  by_cases fresh : memory.registers 12 = 0#256
  · simpa [hashTailSamples, fresh, PMF.map_comp, Function.comp_def] using hashHandler_fresh memory fresh
  · simpa [hashTailSamples, fresh, PMF.pure_map] using hashHandler_found 1810 memory fresh

/-- The complete hash source includes the loader and first-match lookup costs. -/
noncomputable def hashHandlerSamples (count : Nat) (memory : Memory) : PMF (Memory × Nat) :=
  (hashTailSamples (hashScan count memory).1).map fun result =>
    (result.1, result.2 + (hashScan count memory).2 + 27)

/-- The complete hash machine implements its sparse-table source with an exact memory law. -/
theorem hashHandler_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run hashHandler ((hashScan count memory).2 + 1845) ⟨0, memory⟩ =
      (hashHandlerSamples count memory).map (fun result => some (⟨73, result.1⟩, result.2)) := by
  rw [show (hashScan count memory).2 + 1845 = ((hashScan count memory).2 + 27) + 1818 by omega,
    run_after_prefix, hashHandler_start count memory fits counter, PMF.pure_bind]
  dsimp only
  rw [hashHandler_tail]
  simp [hashHandlerSamples, PMF.map_comp, Function.comp_def, Nat.add_assoc]

/-- The exact uniform reply makes the total hash budget linear in its stored entry count. -/
theorem hashHandler_budget (count : Nat) (memory : Memory) :
    hashHandler.size + 1 + (hashScan count memory).2 + 1845 ≤ 6 * count + 1922 := by
  have bounded := tableScan_cost count (tableInitial (hashReady (oracleLoaded memory)))
  change 73 + 1 + (hashScan count memory).2 + 1845 ≤ _
  dsimp [hashScan]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
