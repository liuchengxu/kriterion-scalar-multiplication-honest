import Construction.Simulator.HashHandler
import Proof.Privacy.Simulator.Arithmetic.OracleMetadata
import Proof.Privacy.Simulator.Arithmetic.PairStore
import Proof.Privacy.Simulator.Arithmetic.TableBlock
import Proof.Privacy.Simulator.Arithmetic.WordBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The hash setup implements its complete memory update. -/
theorem hashSetup_memory (memory : Memory) : executeLinear hashSetup memory = hashReady memory := by
  simp [executeLinear, hashSetup, hashReady, LinearInstruction.execute, Arithmetic.eval]

/-- The hash installation implements both RAM writes and its register updates. -/
theorem hashInstall_memory (memory : Memory) : executeLinear hashInstall memory = hashInstalled memory := by
  simp [executeLinear, hashInstall, pairStore, hashInstalled, LinearInstruction.execute,
    Arithmetic.eval, Function.update_comm]

/-- The known branch returns the stored value and its success flag. -/
theorem hashKnown_memory (memory : Memory) : executeLinear hashKnown memory = hashFound memory := by
  simp [executeLinear, hashKnown, hashFound, LinearInstruction.execute, Arithmetic.eval]

/-- The handler contains the metadata loader. -/
theorem hashHandler_load : ContainsLinear hashHandler oracleLoad hashLoadLabels := by
  intro index valid
  have bound : index < 22 := valid
  simp [hashHandler, hashLoadLabels, Nat.min_eq_left (by omega : index ≤ 22),
    Nat.min_eq_left (by omega : index + 1 ≤ 22), bound]

/-- The handler contains the hash setup. -/
theorem hashHandler_setup : ContainsLinear hashHandler hashSetup hashSetupLabels := by
  intro index valid
  have bound : index < 4 := valid
  simp [hashHandler, hashSetupLabels, Nat.min_eq_left (by omega : index ≤ 4),
    Nat.min_eq_left (by omega : index + 1 ≤ 4), show ¬ 22 + index < 22 by omega,
    show 22 ≤ 22 + index by omega, show 22 + index < 26 by omega, Nat.add_assoc]

/-- The handler contains every sparse lookup instruction. -/
theorem hashHandler_table : ContainsTableLookup hashHandler hashTableLabels := by
  intro pc valid
  have different : pc.val + 26 ≠ 35 := by
    intro equal
    apply valid
    apply Fin.ext
    omega
  simp [hashHandler, hashTableLabels, show ¬ pc.val + 26 < 22 by omega,
    show ¬ pc.val + 26 < 26 by omega, show pc.val + 26 < 39 by omega, different]
  rfl

/-- The handler contains the exact 256-bit sampler. -/
theorem hashHandler_word : ContainsWordSampler hashHandler 256 hashWordLabels := by
  intro pc valid
  simp [hashHandler, hashWordLabels, show ¬ pc.val + 39 < 22 by omega,
    show ¬ pc.val + 39 < 26 by omega, show ¬ pc.val + 39 < 39 by omega,
    show pc.val + 39 < 51 by omega]
  rfl

/-- The handler contains every fresh insertion instruction. -/
theorem hashHandler_install : ContainsLinear hashHandler hashInstall hashInstallLabels := by
  intro index valid
  have bound : index < 16 := valid
  simp [hashHandler, hashInstallLabels, bound, show ¬ 51 + index < 22 by omega,
    show ¬ 51 + index < 26 by omega, show ¬ 51 + index < 39 by omega,
    show ¬ 51 + index < 51 by omega, show 51 ≤ 51 + index by omega,
    show 51 + index < 67 by omega, Nat.add_assoc]

/-- The handler contains every known-answer instruction. -/
theorem hashHandler_known : ContainsLinear hashHandler hashKnown hashKnownLabels := by
  intro index valid
  have bound : index < 3 := valid
  simp [hashHandler, hashKnownLabels, Nat.min_eq_left (by omega : index ≤ 3),
    Nat.min_eq_left (by omega : index + 1 ≤ 3), show ¬ 67 + index < 22 by omega,
    show ¬ 67 + index < 26 by omega, show ¬ 67 + index < 39 by omega,
    show ¬ 67 + index < 51 by omega, show ¬ 67 + index < 67 by omega,
    show 67 ≤ 67 + index by omega, show 67 + index < 70 by omega, Nat.add_assoc]

/-- The handler contains the persistent count commit. -/
theorem hashHandler_commit : ContainsLinear hashHandler oracleCommit hashCommitLabels := by
  intro index valid
  have bound : index < 3 := valid
  simp [hashHandler, hashCommitLabels, Nat.min_eq_left (by omega : index ≤ 3),
    Nat.min_eq_left (by omega : index + 1 ≤ 3), show ¬ 70 + index < 22 by omega,
    show ¬ 70 + index < 26 by omega, show ¬ 70 + index < 39 by omega,
    show ¬ 70 + index < 51 by omega, show ¬ 70 + index < 67 by omega,
    show ¬ 70 + index < 70 by omega, show 70 ≤ 70 + index by omega,
    show 70 + index < 73 by omega, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
