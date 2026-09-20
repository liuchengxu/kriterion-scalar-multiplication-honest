import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator

/-- The input loader reads x and y through register eleven and computes their squares. -/
def polynomialInputProgram : List LinearInstruction :=
  [.load 5 11, .constant 2 1, .arithmetic .add 2 11 2, .load 6 2,
    .arithmetic .fieldMul 7 5 5, .arithmetic .fieldMul 8 6 6]

end Kriterion.ArgoMAC.ArithmeticSimulator
