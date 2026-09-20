import Construction.Simulator.GatePolynomial
import Construction.Simulator.RetargetLow

namespace Kriterion.ArgoMAC.ArithmeticSimulator

/-- The preparation loads the requested result and selects the low target word. -/
def gateRetargetPrepare (offset : Nat) : List LinearInstruction :=
  [.constant 3 0, .arithmetic .add 1 4 3, .load 0 13,
    .constant 2 (BitVec.ofNat 256 offset), .arithmetic .add 10 10 2]

/-- The return restores the original gate pointer. -/
def gateRetargetRestore (offset : Nat) : List LinearInstruction :=
  [.constant 2 (BitVec.ofNat 256 offset), .arithmetic .sub 10 10 2]

/-- The retarget tail updates one low word and restores every source pointer. -/
def gateRetargetFinish (offset : Nat) : List LinearInstruction :=
  gateRetargetPrepare offset ++ retargetLow ++ gateRetargetRestore offset

/-- The complete retarget program evaluates the request and updates its low target word. -/
def gateRetarget {coefficients gates : Nat} (terms : List (GateTerm coefficients gates)) (gate : Fin gates) : List LinearInstruction :=
  gatePolynomial terms ++ gateRetargetFinish (254 * gate.val)

end Kriterion.ArgoMAC.ArithmeticSimulator
