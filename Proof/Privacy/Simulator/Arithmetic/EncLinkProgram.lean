import Proof.Privacy.Simulator.Arithmetic.EncLinkPhysicalIndex
import Proof.Privacy.Simulator.Arithmetic.OracleFamilyCutoff
import Proof.Privacy.Simulator.SimulatorMachineLaw

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.OperationalOracle
open Security.SimulatorMachine
noncomputable section

/-- The physical vector uses one canonical finite permutation query per selected label. -/
def encLinkVectorProgram : (count : Nat) →
    (Fin count → EncPRF.PermutationIndex) → (Fin count → Block) →
    Program oracleFamilySpec (Fin count → Block) count
  | 0, _, _ => .pure Fin.elim0
  | count + 1, indices, inputs =>
    .query (.inl (encLinkPhysicalIndex (indices 0), .forward (blockFin (inputs 0)))) fun head =>
      .map (fun (tail : Fin count → Block) => Fin.cases (motive := fun _ => Block) (blockFin.symm head) tail)
        (encLinkVectorProgram count (fun index => indices index.succ) (fun index => inputs index.succ))

/-- The physical coordinate program applies the exact EncPRF whitening and label mask. -/
def encLinkCoordinateProgram (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    Program oracleFamilySpec CoordinateMac coordinateBitCount :=
  .map (fun values => Vector.ofFn fun index => (values index ^^^ keys.second) ^^^ mac[index.val])
    (encLinkVectorProgram coordinateBitCount (fun index => (axis, index))
      (fun index => encodeBit (bits.getLsb index) ^^^ keys.first))

/-- The complete physical link uses the exact hash pair and the two coordinate programs. -/
def encLinkProgram (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    Program oracleFamilySpec InputMac 509 :=
  .query (.inr (curve.result input)) fun encoded =>
    let hash := hashFin.symm encoded
    let keys : WhiteningKeys := ⟨hash.1, hash.2⟩
    .bind (encLinkCoordinateProgram keys .x (BitInput.ofAffine input).xBits mac.x) fun x =>
      .map (fun y => (⟨x, y⟩ : InputMac))
        (encLinkCoordinateProgram keys .y (BitInput.ofAffine input).yBits mac.y)

/-- The physical link uses the established adaptive family completion law. -/
theorem encLinkProgram_adaptive_joint (curve : CurveGateRequest) (input : AffineInput)
    (mac : InputMac) (state : SparseOracleFamily) :
    (oracleFamilyCompletion state).bind
      (fun eager => (encLinkProgram curve input mac).toOracle.run oracleFamilyEager eager) =
      (runSampled oracleFamilySampled (encLinkProgram curve input mac).toOracle state).bind
        (fun result => (oracleFamilyCompletion result.2).map (fun eager => (result.1, eager))) :=
  oracleFamily_adaptive_joint _ state

end
end Kriterion.ArgoMAC.ArithmeticSimulator
