import Proof.Privacy.Simulator.Arithmetic.EncLinkProgram
import Proof.Privacy.Simulator.Arithmetic.ProgramReindex

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security Security.SimulatorMachine
noncomputable section

/-- The link uses only forward EncPRF reads and its bridge hash read. -/
abbrev encLinkReadSpec : OracleSpec where
  Query := (EncPRF.PermutationIndex × Block) ⊕ BaseField
  Answer
    | .inl _ => Block
    | .inr _ => Block × Block

/-- The original source receives the same typed read request. -/
def encLinkOriginalRequest : encLinkReadSpec.Query → spec.Query
  | .inl (index, input) => .read (.encForward index input)
  | .inr key => .read (.hash key)

/-- The original source already uses the selected block and hash-pair types. -/
def encLinkOriginalAnswer : (query : encLinkReadSpec.Query) → spec.Answer (encLinkOriginalRequest query) → encLinkReadSpec.Answer query
  | .inl _, value => value
  | .inr _, value => value

/-- The physical source uses the canonical finite index and block representations. -/
def encLinkPhysicalRequest : encLinkReadSpec.Query → oracleFamilySpec.Query
  | .inl (index, input) => .inl (encLinkPhysicalIndex index, .forward (blockFin input))
  | .inr key => .inr key

/-- The physical reply conversion restores the source block or hash pair. -/
def encLinkPhysicalAnswer : (query : encLinkReadSpec.Query) → oracleFamilySpec.Answer (encLinkPhysicalRequest query) → encLinkReadSpec.Answer query
  | .inl _, value => blockFin.symm value
  | .inr _, value => hashFin.symm value

/-- The common vector syntax makes one typed read for each selected label. -/
def encLinkReadVector : (count : Nat) →
    (Fin count → EncPRF.PermutationIndex) → (Fin count → Block) →
    Program encLinkReadSpec (Fin count → Block) count
  | 0, _, _ => .pure Fin.elim0
  | count + 1, indices, inputs => .query (.inl (indices 0, inputs 0)) fun head =>
      .map (fun (tail : Fin count → Block) => Fin.cases (motive := fun _ => Block) head tail)
        (encLinkReadVector count (fun index => indices index.succ) (fun index => inputs index.succ))

/-- The common coordinate syntax applies the exact two masks. -/
def encLinkReadCoordinate (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    Program encLinkReadSpec CoordinateMac coordinateBitCount :=
  .map (fun values => Vector.ofFn fun index => (values index ^^^ keys.second) ^^^ mac[index.val])
    (encLinkReadVector coordinateBitCount (fun index => (axis, index))
      (fun index => encodeBit (bits.getLsb index) ^^^ keys.first))

/-- The common complete link preserves the original source order. -/
def encLinkReadProgram (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    Program encLinkReadSpec InputMac 509 :=
  .query (.inr (curve.result input)) fun hash =>
    let keys : WhiteningKeys := ⟨hash.1, hash.2⟩
    .bind (encLinkReadCoordinate keys .x (BitInput.ofAffine input).xBits mac.x) fun x =>
      .map (fun y => (⟨x, y⟩ : InputMac))
        (encLinkReadCoordinate keys .y (BitInput.ofAffine input).yBits mac.y)

/-- The common vector becomes the original source vector under its typed inclusion. -/
theorem encLinkReadVector_original (count : Nat) (indices : Fin count → EncPRF.PermutationIndex)
    (inputs : Fin count → Block) :
    (encLinkReadVector count indices inputs).reindex encLinkOriginalRequest encLinkOriginalAnswer = encVector count indices inputs := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [encLinkReadVector, Program.reindex, encLinkOriginalRequest, encLinkOriginalAnswer, encVector, ih]

/-- The common vector becomes the actual physical source vector. -/
theorem encLinkReadVector_physical (count : Nat) (indices : Fin count → EncPRF.PermutationIndex)
    (inputs : Fin count → Block) :
    (encLinkReadVector count indices inputs).reindex encLinkPhysicalRequest encLinkPhysicalAnswer = encLinkVectorProgram count indices inputs := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [encLinkReadVector, Program.reindex, encLinkPhysicalRequest, encLinkPhysicalAnswer, encLinkVectorProgram, ih]

/-- The common link is exactly the original source link under its typed inclusion. -/
theorem encLinkReadProgram_original (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    (encLinkReadProgram curve input mac).reindex encLinkOriginalRequest encLinkOriginalAnswer = link curve input mac := by
  simp only [encLinkReadProgram, Program.reindex, encLinkOriginalRequest, encLinkOriginalAnswer,
    encLinkReadCoordinate, encLinkReadVector_original, link, coordinate]

/-- The common link is exactly the physical source link under finite encoding. -/
theorem encLinkReadProgram_physical (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    (encLinkReadProgram curve input mac).reindex encLinkPhysicalRequest encLinkPhysicalAnswer = encLinkProgram curve input mac := by
  simp only [encLinkReadProgram, Program.reindex, encLinkPhysicalRequest, encLinkPhysicalAnswer,
    encLinkReadCoordinate, encLinkReadVector_physical, encLinkProgram, encLinkCoordinateProgram]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
