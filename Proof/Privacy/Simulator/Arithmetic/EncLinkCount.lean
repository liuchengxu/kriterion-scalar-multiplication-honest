import Proof.Privacy.Simulator.Arithmetic.EncLinkTail

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The controller changes no loop count in RAM. -/
theorem encLinkControlState_counter (memory : Memory) :
    (encLinkControlState memory).1.ram 38#256 = memory.ram 38#256 := by
  unfold encLinkControlState
  split
  · exact congrFun (encLinkReturn_state memory).2.1 _
  · split
    · rw [(encLinkSwitch_state (encLinkCompared memory)).1]
      simp [encLinkCompared]
    · rfl

/-- The controller returns only after the loop count reaches zero. -/
theorem encLinkControlState_target (memory : Memory) :
    (encLinkControlState memory).2.2 =
      if memory.registers 2 = 0#256 then 7466 else 7208 := by
  unfold encLinkControlState
  split
  · rfl
  · split <;> rfl

/-- An accepted query decreases the RAM loop count by exactly one. -/
theorem encLinkAfterQuery_counter (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (encLinkAfterQuery memory).1.ram 38#256 = memory.ram 38#256 - 1#256 := by
  simp only [encLinkAfterQuery, if_neg accepted]
  rw [encLinkControlState_counter, encLinkFinish_ram memory inputSafe countSafe]
  simp

/-- An accepted query returns only when its decreased count is zero. -/
theorem encLinkAfterQuery_target (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (encLinkAfterQuery memory).2.2 =
      if memory.ram 38#256 - 1#256 = 0#256 then 7466 else 7208 := by
  simp only [encLinkAfterQuery, if_neg accepted]
  rw [encLinkControlState_target, encLinkFinish_counter memory countSafe]

/-- Each accepted finite iteration reduces the natural loop count. -/
theorem encLinkAfterQuery_counterNat (memory : Memory) (remaining : Nat)
    (accepted : memory.registers 7 ≠ 0#256)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (counter : memory.ram 38#256 = BitVec.ofNat 256 (remaining + 1)) :
    (encLinkAfterQuery memory).1.ram 38#256 = BitVec.ofNat 256 remaining := by
  rw [encLinkAfterQuery_counter memory accepted inputSafe countSafe, counter, BitVec.ofNat_add]
  simp

/-- The last accepted query selects the final machine return. -/
theorem encLinkAfterQuery_last (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (counter : memory.ram 38#256 = 1#256) :
    (encLinkAfterQuery memory).2.2 = 7466 := by
  rw [encLinkAfterQuery_target memory accepted countSafe, counter]
  simp

end Kriterion.ArgoMAC.ArithmeticSimulator
