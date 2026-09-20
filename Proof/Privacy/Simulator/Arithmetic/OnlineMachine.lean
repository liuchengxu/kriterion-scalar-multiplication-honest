import Construction.Simulator.MemoryLayout
import Construction.Simulator.OnlineInput
import Construction.Simulator.OutputTargets
import Proof.Privacy.Simulator.Arithmetic.EncLinkMachine
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingCode
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStoreMachine
import Proof.Privacy.Simulator.Arithmetic.RetargetSchedule
import Proof.Privacy.Simulator.Arithmetic.GateSchedule

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
noncomputable section
attribute [local irreducible] curveGatePlan pointGatePlan

/-!
## The online machine layout

The machine is one concatenation of proved components. Every boundary below is
`start + width` of the preceding block, so a change to one component width
shifts every later boundary. The widths are read off the components, not
copied: a `.emit` splice of a linear code uses its full `List.length`; a
`relocate` of a `Machine` drops the component's own trailing halt, and of a
`gateLoop` code drops the last two entries (`gateLoop plan` has code length
`1036 * plan.size + 2` and the loop body is `1036 * plan.size`).

| block                        | start     | width      |
|------------------------------|-----------|------------|
| `onlineInputSetup`           | 0         | 1          |
| `onlineInput.code`           | 1         | 97         |
| `onlineOriginalSetup`        | 98        | 3          |
| `selectedLabelStoreCode`     | 101       | 7112       |
| `retargetCurveCode`          | 7213      | 6405       |
| const/load/branch            | 13618     | 3          |
| `onlineSampleSetup`          | 13621     | 1          |
| `onlineSampling.code`        | 13622     | 8771       |
| `onlineTargetSetup`          | 22393     | 4          |
| `outputTargetsMachine.code`  | 22397     | 4288       |
| `onlineRetargetSetup`        | 26685     | 3          |
| `retargetPointCode`          | 26688     | 1401497    |
| `onlineLinkSetup`            | 1428185   | 8          |
| `encLink.code`               | 1428193   | 7466       |
| `onlineOriginalSetup`        | 1435659   | 3          |
| `onlineCurveCode`            | 1435662   | 1315720    |
| const/load/branch            | 2751382   | 3          |
| `onlinePointSetup`           | 2751385   | 3          |
| `onlinePointCode`            | 2751388   | 287353248  |
| `onlineLabelSetup`           | 290104636 | 2          |
| `selectedLabelsCode`         | 290104638 | 200660     |
| halt                         | 290305298 | 2          |

machine size `290305299`, code length `290305300`. Every `Fin 290305300` /
`≤ 290305298` in `onlineBodyLabels`, `onlineBranchLabels` and the `Compiled*`
consumers follows from that. The trailing `.halt` region is two instructions, not
one: `290305298` is the pc of a run that finished the complete label output and
`290305299` is the pc of a run the public sampler cut off. That distinction is
the whole content of the machine protocol's parser, which accepts a run exactly
when its pc is `290305298`; merging the two slots makes a cut-off run parse as a
completed one. `onlineMachine_halts` therefore states them as a conjunction and
`onlineMachine_cutoff` names the second.
`onlineTargetSetup` points register ten `onlineSampleBase + 91`: `onlineWords`
stores `onlineScaleSchedule.wordsLength = 91` scale words before the 90 point
words (`onlineWords_length = 361`).

## The online buffer bases

`onlineBuffer_bounds` fixes the gaps by `decide`, so they are requirements, not
free choices: five words for the `onlineInput` record, then the 361 sampled
words, then the 273 target words (91 rows times three coordinates), then the 508
original labels, then the 508 linked labels.

| buffer              | base (relative to `privateBase`) | gap from the previous buffer |
|---------------------|----------------------------------|------------------------------|
| `onlineInputBase`   | 838208                           | 838208 (the offline words)   |
| `onlineSampleBase`  | 838213                           | 5                            |
| `onlineTargetBase`  | 838574                           | 361                          |
| `onlineOriginalBase`| 838847                           | 273                          |
| `onlineLinkedBase`  | 839355                           | 508                          |
-/

/-- The five-word record `onlineInput` writes at register ten. -/
def onlineInputBase : Nat := privateBase + 838208
/-- The 361 words `onlineSampling` writes: 91 scales then 90 points. -/
def onlineSampleBase : Nat := privateBase + 838213
/-- The 273 words `outputTargetsMachine` writes: 91 rows of three coordinates. -/
def onlineTargetBase : Nat := privateBase + 838574
/-- The 508 original labels `encLink` reads. -/
def onlineOriginalBase : Nat := privateBase + 838847
/-- The 508 linked labels `encLink` writes. -/
def onlineLinkedBase : Nat := privateBase + 839355

/-- Each setup block installs the exact pointers used by its next proved component. -/
def onlineInputSetup : List LinearInstruction := [.constant 10 (BitVec.ofNat 256 onlineInputBase)]
def onlineOriginalSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineOriginalBase)]
def onlineSampleSetup : List LinearInstruction := [.constant 10 (BitVec.ofNat 256 onlineSampleBase)]
def onlineTargetSetup : List LinearInstruction :=
  [.constant 10 (BitVec.ofNat 256 (onlineSampleBase + 91)), .constant 11 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineSampleBase), .constant 13 (BitVec.ofNat 256 onlineTargetBase)]
def onlineRetargetSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineTargetBase)]
def onlineLinkSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 onlineOriginalBase), .constant 14 (BitVec.ofNat 256 onlineLinkedBase),
    .constant 0 (BitVec.ofNat 256 onlineInputBase), .load 12 0,
    .constant 0 (BitVec.ofNat 256 (onlineInputBase + 1)), .load 13 0,
    .constant 0 (BitVec.ofNat 256 privateBase), .load 8 0]
def onlinePointSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase),
    .constant 14 (BitVec.ofNat 256 onlineLinkedBase)]
def onlineLabelSetup : List LinearInstruction :=
  [.constant 11 (BitVec.ofNat 256 privateBase), .constant 12 (BitVec.ofNat 256 onlineInputBase)]

/-- Each local return maps directly to its next global instruction. -/
def onlineBodyLabels (start length : Nat) (inside : start + length ≤ 290305298)
    (normal : Fin 290305300) (pc : Nat) : Fin 290305300 :=
  if active : pc < length then ⟨start + pc, by omega⟩ else normal

/-- A sampler cutoff maps to the shared cutoff exit. -/
def onlineBranchLabels (start length : Nat) (inside : start + length ≤ 290305298)
    (normal : Fin 290305300) (pc : Nat) : Fin 290305300 :=
  if active : pc < length then ⟨start + pc, by omega⟩
  else if pc = length then normal else 290305299

private noncomputable def onlineCurvePackage (attempts : Nat) :
    {code : Vector (Instruction 1315722) 1315722 // code = (gateLoop curveGatePlan attempts (by decide)).code} :=
  Classical.choice ⟨⟨(gateLoop curveGatePlan attempts (by decide)).code, rfl⟩⟩
private noncomputable def onlinePointPackage (attempts : Nat) :
    {code : Vector (Instruction 287353250) 287353250 // code = (gateLoop pointGatePlan attempts (by decide)).code} :=
  Classical.choice ⟨⟨(gateLoop pointGatePlan attempts (by decide)).code, rfl⟩⟩
def onlineCurveCode (attempts : Nat) : Vector (Instruction 1315722) 1315722 := (onlineCurvePackage attempts).val
def onlinePointCode (attempts : Nat) : Vector (Instruction 287353250) 287353250 := (onlinePointPackage attempts).val
theorem onlineCurveCode_eq (attempts : Nat) : onlineCurveCode attempts = (gateLoop curveGatePlan attempts (by decide)).code :=
  (onlineCurvePackage attempts).property
theorem onlinePointCode_eq (attempts : Nat) : onlinePointCode attempts = (gateLoop pointGatePlan attempts (by decide)).code :=
  (onlinePointPackage attempts).property

/-- The online table includes input, private arithmetic, oracle programming, and final labels.
The valid path runs the label link before both fixed-gate phases.
The absent-output path runs only the curve phase.
Every sampler cutoff reaches the separate final cutoff label. -/
def onlineInstruction (attempts : Nat) (pc : Fin 290305300) : Instruction 290305300 :=
  if block : pc.val < 1 then
    (onlineInputSetup[pc.val]'(by change pc.val < 1; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 98 then
    relocate (fun label => onlineBodyLabels 1 97 (by decide) 98 label.val)
      (onlineInput.code[pc.val - 1]'(by change pc.val - 1 < 98; omega))
  else if block : pc.val < 101 then
    (onlineOriginalSetup[pc.val - 98]'(by change pc.val - 98 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 7213 then
    (selectedLabelStoreCode[pc.val - 101]'(by rw [selectedLabelStoreCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 13618 then
    (retargetCurveCode[pc.val - 7213]'(by rw [retargetCurveCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 13621 then
    match pc.val with
    | 13618 => .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 13619
    | 13619 => .load 0 0 13620
    | _ => .branch 0 1435659 13621
  else if block : pc.val < 13622 then
    (onlineSampleSetup[pc.val - 13621]'(by change pc.val - 13621 < 1; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 22393 then
    relocate (fun label => onlineBodyLabels 13622 8771 (by decide) 22393 label.val)
      ((onlineSampling attempts).code[pc.val - 13622]'(by change pc.val - 13622 < 8772; omega))
  else if block : pc.val < 22397 then
    (onlineTargetSetup[pc.val - 22393]'(by change pc.val - 22393 < 4; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 26685 then
    relocate (fun label => onlineBodyLabels 22397 4288 (by decide) 26685 label.val)
      (outputTargetsMachine.code[pc.val - 22397]'(by change pc.val - 22397 < 4289; omega))
  else if block : pc.val < 26688 then
    (onlineRetargetSetup[pc.val - 26685]'(by change pc.val - 26685 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1428185 then
    (retargetPointCode[pc.val - 26688]'(by rw [retargetPointCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1428193 then
    (onlineLinkSetup[pc.val - 1428185]'(by change pc.val - 1428185 < 8; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 1435659 then
    relocate (fun label => onlineBranchLabels 1428193 7466 (by decide) 1435659 label.val)
      ((encLink attempts).code[pc.val - 1428193]'(by change pc.val - 1428193 < 7468; omega))
  else if block : pc.val < 1435662 then
    (onlineOriginalSetup[pc.val - 1435659]'(by change pc.val - 1435659 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 2751382 then
    relocate (fun label => onlineBranchLabels 1435662 1315720 (by decide) 2751382 label.val)
      ((onlineCurveCode attempts)[pc.val - 1435662]'(by omega))
  else if block : pc.val < 2751385 then
    match pc.val with
    | 2751382 => .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 2751383
    | 2751383 => .load 0 0 2751384
    | _ => .branch 0 290104636 2751385
  else if block : pc.val < 2751388 then
    (onlinePointSetup[pc.val - 2751385]'(by change pc.val - 2751385 < 3; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 290104636 then
    relocate (fun label => onlineBranchLabels 2751388 287353248 (by decide) 290104636 label.val)
      ((onlinePointCode attempts)[pc.val - 2751388]'(by omega))
  else if block : pc.val < 290104638 then
    (onlineLabelSetup[pc.val - 290104636]'(by change pc.val - 290104636 < 2; omega)).emit ⟨pc.val + 1, by omega⟩
  else if block : pc.val < 290305298 then
    (selectedLabelsCode[pc.val - 290104638]'(by rw [selectedLabelsCode_length]; omega)).emit ⟨pc.val + 1, by omega⟩
  else .halt

/-- The fixed table retains its symbolic instruction function. -/
private noncomputable def onlineMachineCodePackage (attempts : Nat) :
    {code : Vector (Instruction 290305300) 290305300 // code = Vector.ofFn (onlineInstruction attempts)} :=
  Classical.choice ⟨⟨Vector.ofFn (onlineInstruction attempts), rfl⟩⟩
def onlineMachineCode (attempts : Nat) : Vector (Instruction 290305300) 290305300 :=
  (onlineMachineCodePackage attempts).val

/-- Each table lookup selects one instruction without expanding the table. -/
theorem onlineMachineCode_get (attempts index : Nat) (inside : index < 290305300) :
    (onlineMachineCode attempts)[index] = onlineInstruction attempts ⟨index, inside⟩ := by
  rw [onlineMachineCode, (onlineMachineCodePackage attempts).property, Vector.getElem_ofFn]

/-- The machine keeps its fixed table size separate from its symbolic instruction code. -/
abbrev onlineMachine (attempts : Nat) : Machine := ⟨290305299, onlineMachineCode attempts, by decide⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
