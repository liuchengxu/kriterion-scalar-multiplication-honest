import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCounts
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward answer tail preserves the stored oracle state on both cutoff branches. -/
theorem publicForwardTail_ram (count : Nat) (memory : Memory) :
    (publicForwardTail count memory).1.ram = memory.ram := by
  unfold publicForwardTail
  split
  · rfl
  · rw [wordOutput_ram]
    exact (overlayForward_data count memory).1

/-- The inverse answer tail preserves the stored oracle state on both cutoff branches. -/
theorem publicInverseTail_ram (memory : Memory) :
    (publicInverseTail memory).1.ram = memory.ram := by
  unfold publicInverseTail
  split
  · rfl
  · exact wordOutput_ram 128 memory

/-- The hash answer tail preserves the stored oracle state. -/
theorem publicHashTail_ram (memory : Memory) :
    (publicHashTail memory).1.ram = memory.ram := by
  unfold publicHashTail
  split
  · rfl
  · exact hashOutput_ram memory

/-- Inverse preparation preserves every public oracle cell. -/
theorem publicInversePrepared_public (count : Nat) (memory : Memory) (oracle : Fin 15749)
    (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (publicInversePrepared count memory).ram (oracleAddress oracle table offset) = memory.ram (oracleAddress oracle table offset) := by
  rw [(publicInversePrepared_data count memory).1]
  exact oracleLoadRam_public memory oracle table offset fits

end Kriterion.ArgoMAC.ArithmeticSimulator
