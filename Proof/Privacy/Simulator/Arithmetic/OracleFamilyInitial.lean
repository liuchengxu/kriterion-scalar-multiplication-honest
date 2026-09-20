import Proof.Privacy.Simulator.Arithmetic.OracleFamilyMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The initial physical family has no finite oracle records. -/
def emptyOracleFamily : SparseOracleFamily := ⟨fun _ => ProgrammedPermutation.empty (2 ^ 128), []⟩

/-- The empty finite family fits all physical oracle regions. -/
theorem emptyOracleFamily_fits : OracleFamilyFits emptyOracleFamily := by
  constructor <;> intros <;> norm_num [emptyOracleFamily, ProgrammedPermutation.empty, SparsePermutation.empty]

/-- Zero public headers represent the exact empty oracle family. -/
theorem emptyOracleFamily_memory (ram : Word → Word)
    (zero : ∀ oracle table, ram (oracleAddress oracle table 0) = 0) :
    OracleFamilyMemory ram emptyOracleFamily := by
  constructor
  · intro index
    constructor
    · refine ⟨⟨rfl, rfl, trivial, trivial⟩, ?_⟩
      exact zero index.castSucc 0
    · exact ⟨zero index.castSucc 2, trivial⟩
  · exact ⟨zero 15748 0, trivial⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
