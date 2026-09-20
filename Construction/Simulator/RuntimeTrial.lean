import Construction.Simulator.RangeWidth
import Construction.Simulator.WordSampler
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The runtime trial retains the width-routine labels. -/
def runtimeWidthLabels (pc : Fin 10) : Fin 27 := ⟨pc.val, by omega⟩

/-- The runtime trial places the sampling loop after the width routine. -/
def runtimeWordLabels (pc : Fin 13) : Fin 27 := ⟨pc.val + 6, by omega⟩

/-- The trial reads its range from register five and returns its acceptance flag in register seven. -/
def runtimeTrial : Machine := ⟨26,
  Vector.ofFn (fun pc : Fin 27 =>
    if width : pc.val < 9 then
      relocate runtimeWidthLabels (rangeWidth.code[pc.val]'(by change pc.val < 10; omega))
    else if loop : pc.val < 18 then
      relocate runtimeWordLabels ((wordSampler 0).code[pc.val - 6]'(by change pc.val - 6 < 13; omega))
    else match pc.val with
      | 18 => .branch 5 19 23
      | 19 => .coin 1 20
      | 20 => .pop 1 26 21 22
      | 21 => .constant 6 0 24
      | 22 => .constant 6 1 24
      | 23 => .constant 6 0 25
      | 24 => .arithmetic .less 7 6 1 26
      | 25 => .arithmetic .less 7 0 5 26
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
