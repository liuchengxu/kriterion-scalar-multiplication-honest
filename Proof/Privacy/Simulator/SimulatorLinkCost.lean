import Proof.Privacy.Simulator.SimulatorOracleProgram

namespace Kriterion.ArgoMAC.Security.SimulatorMachine.LinkCost
open BN254 Cryptography

/-- The counter charges a bit read, a bit encoding, a key read, and an XOR. -/
def queryInput (keys : WhiteningKeys) (bits : BitVec coordinateBitCount)
    (index : Fin coordinateBitCount) : Block × Nat :=
  (encodeBit (bits.getLsb index) ^^^ keys.first, 4)

/-- The counter charges two reads and two XOR operations. -/
def answerValue (keys : WhiteningKeys) (mac : CoordinateMac)
    (index : Fin coordinateBitCount) (answer : Block) : Block × Nat :=
  ((answer ^^^ keys.second) ^^^ mac[index.val], 4)

/-- The program stores each answer in an array. The counter includes one push and
three index, request, and continuation construction operations per query. -/
def coordinatePrefix (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    (count : Nat) → count ≤ coordinateBitCount →
      Program spec (Vector Block count × Nat) count
  | 0, _ => .pure (#v[], 0)
  | count + 1, bounded =>
    let index : Fin coordinateBitCount := ⟨count, by omega⟩
    let input := queryInput keys bits index
    .query (.read (.encForward (axis, index) input.1)) fun answer =>
      let value := answerValue keys mac index answer
      .map (fun previous => (previous.1.push value.1, previous.2 + input.2 + value.2 + 4))
        (coordinatePrefix keys axis bits mac count (by omega))

private def coordinateValues (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) (state : SimulatorState)
    (index : Fin coordinateBitCount) : Block :=
  (state.encOracle.permutation (axis, index)
    (encodeBit (bits.getLsb index) ^^^ keys.first) ^^^ keys.second) ^^^ mac[index.val]

theorem coordinatePrefix_run (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) (count : Nat)
    (bounded : count ≤ coordinateBitCount) (state : SimulatorState) :
    (coordinatePrefix keys axis bits mac count bounded).run handler state =
      ((Vector.ofFn (fun index : Fin count => coordinateValues keys axis bits mac state
        ⟨index.val, lt_of_lt_of_le index.isLt bounded⟩), 12 * count), state) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [coordinatePrefix, Program.run, handler, ih, queryInput, answerValue]
    apply congrArg (fun value => (value, state))
    apply Prod.ext
    · apply Vector.ext
      intro index valid
      by_cases before : index < count
      · simp only [Vector.getElem_push, before, ↓reduceDIte, Vector.getElem_ofFn]
      · have last : index = count := by omega
        subst index
        simp only [Vector.getElem_push, lt_self_iff_false, ↓reduceDIte, Vector.getElem_ofFn]
        rfl
    · omega

/-- Every oracle handler gives the same local operation count. -/
theorem coordinatePrefix_cost {State : Type} (oracleHandler : OracleHandler spec State)
    (keys : WhiteningKeys) (axis : EncPRF.Coordinate) (bits : BitVec coordinateBitCount)
    (mac : CoordinateMac) (count : Nat) (bounded : count ≤ coordinateBitCount) (state : State) :
    ((coordinatePrefix keys axis bits mac count bounded).run oracleHandler state).1.2 =
      12 * count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    simp only [coordinatePrefix, Program.run, queryInput, answerValue]
    rw [ih]
    omega

/-- The coordinate program has 254 oracle calls and 3048 local primitive operations. -/
def coordinateWithCost (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) :
    Program spec (CoordinateMac × Nat) coordinateBitCount :=
  coordinatePrefix keys axis bits mac coordinateBitCount (Nat.le_refl _)

theorem coordinateWithCost_run (keys : WhiteningKeys) (axis : EncPRF.Coordinate)
    (bits : BitVec coordinateBitCount) (mac : CoordinateMac) (state : SimulatorState) :
    (coordinateWithCost keys axis bits mac).run handler state =
      ((EncPRF.transformCoordinateMac state.encOracle keys axis bits mac, 3048), state) := by
  rw [coordinateWithCost, coordinatePrefix_run]
  rfl

/-- The caller computes the hash input from its cached target arrays.
The counter includes four input reads, two field-to-word conversions, two key reads,
and six record and program construction operations. -/
def linkWithCost (hashInput : BaseField) (input : AffineInput) (mac : InputMac) :
    Program spec (InputMac × Nat) 509 :=
  .query (.read (.hash hashInput)) fun hash =>
    let keys : WhiteningKeys := ⟨hash.1, hash.2⟩
    let bits := BitInput.ofAffine input
    .bind (coordinateWithCost keys .x bits.xBits mac.x) fun x =>
      .map (fun y => ((⟨x.1, y.1⟩ : InputMac), x.2 + y.2 + 14))
        (coordinateWithCost keys .y bits.yBits mac.y)

theorem linkWithCost_run (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (hashInput : BaseField) (cached : hashInput = curve.result input) (state : SimulatorState) :
    (linkWithCost hashInput input mac).run handler state =
      ((linkedPointInputMac state curve input mac, 6110), state) := by
  subst hashInput
  simp only [linkWithCost, Program.run, handler, coordinateWithCost_run]
  rfl

/-- The local operation count does not depend on oracle answers or oracle state. -/
theorem linkWithCost_cost {State : Type} (oracleHandler : OracleHandler spec State)
    (hashInput : BaseField) (input : AffineInput) (mac : InputMac) (state : State) :
    ((linkWithCost hashInput input mac).run oracleHandler state).1.2 = 6110 := by
  simp only [linkWithCost, Program.run, coordinateWithCost, coordinatePrefix_cost]
  rfl

end Kriterion.ArgoMAC.Security.SimulatorMachine.LinkCost
