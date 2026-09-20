import Proof.Privacy.Simulator.Arithmetic.GateCodeInputs
import Proof.Privacy.Simulator.Arithmetic.SharedFamilyReindex

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.SharedSimulatorMachine

/-- Each compiled slot uses the exact physical index of its typed shared command. -/
theorem gateCodeAt_index (location : Pipeline.FixedKeyLocation) (isX : Bool)
    (start gates gate : Nat) (bit : Fin 254) (slot : Fin 3) :
    (gateCodeAt location isX start gates gate bit).oracle slot =
      (sharedPhysicalIndex (.inl (Shared.fixedIndex (fixedKeyIndex location bit.val (.hash slot))))).val := by
  rw [sharedPhysicalIndex_fixed]
  simp only [gateCodeAt, Shared.fixedIndex, fixedKeyIndex, Shared.slotIndex, coordinateBitCount, Nat.mod_eq_of_lt bit.isLt]

end Kriterion.ArgoMAC.ArithmeticSimulator
