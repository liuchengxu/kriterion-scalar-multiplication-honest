import Construction.Simulator.FieldFold

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A polynomial factor names one of four preserved input registers. -/
def polynomialFactorRegister (factor : Fin 4) : Register := ⟨5 + factor.val, by omega⟩

/-- The fixed factor instructions multiply the term accumulator in register zero. -/
def polynomialFactors (factors : List (Fin 4)) : List LinearInstruction :=
  factors.map fun factor => .arithmetic .fieldMul 0 0 (polynomialFactorRegister factor)

/-- A polynomial term reads a coefficient or a complete 254-word field-bit table. -/
structure PolynomialTerm where
  offset : Nat
  folded : Bool
  factors : List (Fin 4)

/-- The term compiler emits only fixed RAM loads and field instructions. -/
def polynomialTermRead (term : PolynomialTerm) : List LinearInstruction :=
  if term.folded then fieldFold 254 term.offset else
    [.constant 2 (BitVec.ofNat 256 term.offset), .arithmetic .add 2 10 2, .load 0 2]

/-- Each compiled term adds its value to register four. -/
def polynomialTerm (term : PolynomialTerm) : List LinearInstruction :=
  polynomialTermRead term ++ polynomialFactors term.factors ++ [.arithmetic .fieldAdd 4 4 0]

/-- The polynomial compiler preserves source pointers and processes each fixed term. -/
def polynomial (terms : List PolynomialTerm) : List LinearInstruction :=
  [.constant 4 0] ++ terms.flatMap polynomialTerm

end Kriterion.ArgoMAC.ArithmeticSimulator
