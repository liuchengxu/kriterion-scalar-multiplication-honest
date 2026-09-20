import Construction.Simulator.FieldPolynomial

namespace Kriterion.ArgoMAC.ArithmeticSimulator

/-- A gate term names one stored coefficient or one stored target table. -/
inductive GateTerm (coefficients gates : Nat) where
  | coefficient (index : Fin coefficients) (factors : List (Fin 4))
  | target (index : Fin gates) (factors : List (Fin 4))

/-- Each gate term has a fixed field-word offset and a fixed factor list. -/
def GateTerm.compile {coefficients gates : Nat} : GateTerm coefficients gates → PolynomialTerm
  | .coefficient index factors => ⟨3 * gates * 254 + index.val, false, factors⟩
  | .target index factors => ⟨254 * index.val, true, factors⟩

/-- The gate compiler emits the complete fixed polynomial program. -/
def gatePolynomial {coefficients gates : Nat} (terms : List (GateTerm coefficients gates)) : List LinearInstruction :=
  polynomial (terms.map GateTerm.compile)

/-- The curve request uses its three coefficients and five target tables. -/
def curveTerms : List (GateTerm 3 5) :=
  [.coefficient 0 [], .coefficient 1 [2, 0], .coefficient 2 [3],
    .target 0 [2], .target 3 [1], .target 1 [0], .target 4 [], .target 2 []]

/-- The X request uses its five coefficients and four target tables. -/
def xTerms : List (GateTerm 5 4) :=
  [.coefficient 0 [], .coefficient 1 [0], .coefficient 2 [1], .coefficient 3 [0, 1], .coefficient 4 [3],
    .target 0 [0], .target 1 [1], .target 3 [], .target 2 []]

/-- The Y request uses its four coefficients and the three target tables its
x-only cubic basis, y6, x7, and x9, reads. -/
def yTerms : List (GateTerm 4 3) :=
  [.coefficient 0 [], .coefficient 1 [0], .coefficient 2 [2], .coefficient 3 [2, 0],
    .target 0 [2], .target 1 [0], .target 2 []]

/-- The Z request uses its five coefficients and five target tables. -/
def zTerms : List (GateTerm 5 5) :=
  [.coefficient 0 [], .coefficient 1 [1], .coefficient 2 [0, 1], .coefficient 3 [2], .coefficient 4 [3],
    .target 0 [0], .target 3 [0], .target 1 [1], .target 4 [], .target 2 []]

end Kriterion.ArgoMAC.ArithmeticSimulator
