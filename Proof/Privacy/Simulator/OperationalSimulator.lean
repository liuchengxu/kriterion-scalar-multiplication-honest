import Proof.Privacy.Simulator.SimulatorSampling
import Proof.Privacy.Simulator.SimulatorExecution
import Proof.Privacy.Simulator.PointSampler

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
namespace SimulatorSampling

/-- The scalar sampler uses the canonical residue enumeration. -/
def scalarEquiv : Fin scalarFieldModulus ≃ ScalarField where
  toFun value := value.val
  invFun value := ⟨value.val, value.val_lt⟩
  left_inv value := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt
  right_inv value := ZMod.natCast_zmod_val value

def scalar : Code ScalarField 1 :=
  (Code.draw scalarFieldModulus (by decide)).map scalarEquiv

theorem scalar_uniform : Uniform scalar := by
  apply uniform_equiv (code := Code.draw scalarFieldModulus (by decide))
  rfl

/-- The point sampler uses one bounded scalar draw and the binary group algorithm. -/
def point [FieldCertificate] : Code Point 1 := scalar.map samplePoint

theorem point_uniform [FieldCertificate] [GroupCertificate] : Uniform point := by
  unfold Uniform point
  rw [Code.map_law, scalar_uniform, samplePoint_uniform]

/-- The online sampler uses 90 points and 91 nonzero scales. -/
def online [FieldCertificate] :
    Code ((Fin 90 → Point) × (Fin FieldMacToECMac.outputMacCount → NonZeroBase)) 181 :=
  (point.arrayFunction 90).pair (scale.arrayFunction FieldMacToECMac.outputMacCount)

theorem online_uniform [FieldCertificate] [GroupCertificate] : Uniform online :=
  uniform_pair (point.arrayFunction_uniform point_uniform _)
    (scale.arrayFunction_uniform scale_uniform _)

theorem online_drawSizeLe [FieldCertificate] : online.DrawSizeLe (2 ^ 256) := by
  apply Code.pair_drawSizeLe
  · apply Code.arrayFunction_drawSizeLe
    apply Code.map_drawSizeLe
    exact Code.map_drawSizeLe _ _ (by change scalarFieldModulus ≤ 2 ^ 256; decide)
  · exact scale.arrayFunction_drawSizeLe scale_drawSizeLe _

/-- This deterministic map attaches an oracle environment to the private coin. -/
def attachOracles (oracles : SimulatorOracleCoin) (coin : OfflineCoin) : CircuitSimulatorState :=
  (coinEquiv (coin, oracles)).state

/-- This program samples only the private data of the offline simulator. -/
def garble (oracles : SimulatorOracleCoin) : Code (Pipeline.Table × CircuitSimulatorState) 838208 :=
  offline.map fun coin =>
    let state := attachOracles oracles coin
    (state.table, state)

local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩

/-- The private program and independent oracle environment give the original offline law. -/
theorem garble_law [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (topology : Garbling.Topology) :
    (PMF.uniformOfFintype SimulatorOracleCoin).bind (fun oracles => (garble oracles).law) =
      concreteCircuitSimulator.simulateGarble parameter topology := by
  have law := congrArg (fun distribution : PMF SimulatorCoin =>
      distribution.map (fun coin => (coin.state.table, coin.state))) offline_with_oracles
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at law
  simpa only [garble, Code.map_law, attachOracles, concreteCircuitSimulator, circuitSimulator,
    simulatorStateTape, PMF.map_comp, Function.comp_def] using law

/-- This program separates online random draws from the selected-path computation. -/
def encode [FieldCertificate] [GroupCertificate] (state : CircuitSimulatorState)
    (input : AffineInput) (output : Option Point) :
    Code (Garbling.Labels × CircuitSimulatorState) (if output.isSome then 181 else 0) :=
  match output with
  | none => .pure (state.labels input,
      { state with oracle := (programGateSchedule state.oracle
        ((state.selectedCurve input).schedule input (state.labels input).inputMac)) })
  | some result => online.map fun sample =>
      (state.labels input, state.programForOutput input result (Vector.ofFn sample.1) sample.2)

set_option maxRecDepth 4096 in
/-- The explicit online sampler has exactly the existing simulator's distribution. -/
theorem encode_law [FieldCertificate] [GroupCertificate] (state : CircuitSimulatorState)
    (input : AffineInput) (output : Option Point) :
    (encode state input output).law = concreteCircuitSimulator.simulateEncode state input output := by
  cases output with
  | none => rfl
  | some result =>
    simp only [encode, Code.map_law]
    rw [online_uniform]
    rfl

end SimulatorSampling
end Kriterion.ArgoMAC.Security
