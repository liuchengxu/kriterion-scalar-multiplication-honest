import Construction.Simulator.GatePolynomial
import Proof.Privacy.Simulator.Arithmetic.GatePrivateLayout
import Proof.Privacy.Simulator.Arithmetic.FieldPolynomial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling

/-- The typed gate source gives each fixed term its sampled coefficient or folded target. -/
def gateSourceValue {coefficients gates : Nat} (data : GateData coefficients gates) (term : PolynomialTerm) : BaseField :=
  if term.folded then
    if inside : term.offset / 254 < gates then DigitAdaptor.fromBits (data.2.2.2 ⟨term.offset / 254, inside⟩) else 0
  else if inside : term.offset - 3 * gates * 254 < coefficients then data.1 ⟨term.offset - 3 * gates * 254, inside⟩ else 0

/-- Each source term carries its exact typed field value. -/
def GateTerm.value {coefficients gates : Nat} (data : GateData coefficients gates) : GateTerm coefficients gates → BaseField
  | .coefficient index _ => data.1 index
  | .target index _ => DigitAdaptor.fromBits (data.2.2.2 index)

/-- A term source uses the same factor list as its fixed compiled instructions. -/
def GateTerm.factors {coefficients gates : Nat} : GateTerm coefficients gates → List (Fin 4)
  | .coefficient _ factors | .target _ factors => factors

/-- The fixed address decoder preserves each typed gate source. -/
theorem gateSourceValue_compile {coefficients gates : Nat} (data : GateData coefficients gates)
    (term : GateTerm coefficients gates) : gateSourceValue data term.compile = term.value data := by
  cases term with
  | coefficient index factors => simp [gateSourceValue, GateTerm.compile, GateTerm.value, index.isLt]
  | target index factors => simp [gateSourceValue, GateTerm.compile, GateTerm.value, index.isLt]

/-- Every compiled gate term reads the exact offline source words. -/
theorem gateTerm_source {coefficients gates : Nat} (data : GateData coefficients gates)
    (base : Memory) (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule coefficients gates).words data))
    (term : GateTerm coefficients gates) :
    PolynomialSource term.compile base.ram (base.registers 10) (gateSourceValue data term.compile) := by
  rw [gateSourceValue_compile]
  cases term with
  | coefficient index factors =>
      change base.ram (base.registers 10 + BitVec.ofNat 256 (3 * gates * 254 + index.val)) = BitVec.ofNat 256 (data.1 index).val
      simpa only [Nat.zero_add, coordinateBitCount] using gateData_coefficient coefficients gates data base.ram (base.registers 10) 0 index stored
  | target index factors =>
      refine ⟨data.2.2.2 index, rfl, ?_⟩
      intro bit
      simpa only [Nat.zero_add, coordinateBitCount, GateTerm.compile] using gateData_target coefficients gates data base.ram (base.registers 10) 0 index bit stored

/-- The compiled gate polynomial returns the sum of its exact typed terms. -/
theorem gatePolynomial_value {coefficients gates : Nat} (terms : List (GateTerm coefficients gates))
    (data : GateData coefficients gates) (values : Fin 4 → BaseField) (base : Memory)
    (stored : WordsAt base.ram (base.registers 10) 0 ((gateDataSchedule coefficients gates).words data))
    (encoded : ∀ factor, base.registers (polynomialFactorRegister factor) = BitVec.ofNat 256 (values factor).val) :
    (executeLinear (gatePolynomial terms) base).registers 4 = BitVec.ofNat 256
      (terms.foldl (fun (sum : BaseField) (term : GateTerm coefficients gates) =>
        sum + term.factors.foldl (fun product factor => product * values factor) (term.value data)) 0).val := by
  have sources : ∀ term ∈ terms.map GateTerm.compile,
      PolynomialSource term base.ram (base.registers 10) (gateSourceValue data term) := by
    intro term member
    obtain ⟨source, _, same⟩ := List.mem_map.mp member
    rw [← same]
    exact gateTerm_source data base stored source
  have computed := polynomial_value (terms.map GateTerm.compile) values (gateSourceValue data) base sources encoded
  have factors (term : GateTerm coefficients gates) : term.compile.factors = term.factors := by cases term <;> rfl
  simpa only [gatePolynomial, List.foldl_map, gateSourceValue_compile, factors] using computed

end Kriterion.ArgoMAC.ArithmeticSimulator
