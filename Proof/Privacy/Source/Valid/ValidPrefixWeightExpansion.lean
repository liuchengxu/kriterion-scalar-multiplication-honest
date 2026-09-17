import Proof.Privacy.Source.Valid.ValidPrefixPhaseWeight

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1 instFintypeCircuitMaskTables

private theorem sourceGoodMass_congr {Source Output : Type*}
    (left right : PMF Source) (kernel : Source → PMF Output)
    (first second : Set Source) (output : Output)
    (samplesEq : left = right) (badEq : first = second) :
    sourceGoodMass left kernel first output = sourceGoodMass right kernel second output := by
  rw [samplesEq, badEq]

private def prefixChoose {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (rest : SourceOracleRest) :=
  gateSourceChoose adversary parameter auxiliary table rest.2

set_option maxRecDepth 4096 in
private theorem prefixWeight_eq [fieldCert : FieldCertificate] [groupCert : GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) (randomness : Garbling.Randomness)
    (tag : (RawCircuitGate → FullHashLift) × CircuitMaskTables) :
    sourceGoodMass
      (prefixChoose adversary parameter auxiliary
        (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1
          (maskRetainedTape randomness).2.2.1.2.value (retainedSourceRows scalar (maskRetainedTape randomness))
          (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)))
        (maskRetainedTape randomness).2.2)
      (fun selected => fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback (randomness, tag, selected))
      {selected | {coin | fullGatePrefixBad coin} (randomness, tag, selected)} output =
    validPrefixPhaseWeight adversary parameter auxiliary scalar fallback output randomness tag := by
  apply sourceGoodMass_congr
  · rfl
  · rfl

set_option maxRecDepth 4096 in
private theorem prefixWeight_sum_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) :
    (∑' randomness, (randomTape witness parameter) randomness *
      ∑' tag : (RawCircuitGate → FullHashLift) × CircuitMaskTables,
        (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)) tag *
          sourceGoodMass
            (prefixChoose adversary parameter auxiliary
              (circuitMaskSourceTable (maskRetainedTape randomness).2.2.1.1
                (maskRetainedTape randomness).2.2.1.2.value (retainedSourceRows scalar (maskRetainedTape randomness))
                (decodeFullSource (tag.1, sharedCircuitHashRest randomness tag.2)))
              (maskRetainedTape randomness).2.2)
            (fun selected => fullGatePrefixKernel scalar
              (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
              fallback (randomness, tag, selected))
            {selected | {coin | fullGatePrefixBad coin} (randomness, tag, selected)} output) =
    ∑' randomness, (randomTape witness parameter) randomness *
      ∑' tag : (RawCircuitGate → FullHashLift) × CircuitMaskTables,
        (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)) tag *
          validPrefixPhaseWeight adversary parameter auxiliary scalar fallback output randomness tag := by
  apply tsum_congr
  intro randomness
  apply congrArg ((randomTape witness parameter) randomness * ·)
  apply tsum_congr
  intro tag
  apply congrArg ((PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitMaskTables)) tag * ·)
  exact prefixWeight_eq adversary parameter auxiliary scalar fallback output randomness tag

set_option maxRecDepth 4096 in
private theorem originalPrefix_eq [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) :
    sourceGoodMass (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2) fallback)
      {coin | fullGatePrefixBad coin} output =
    sourceGoodMass (fullGatePrefixSamples scalar witness parameter (prefixChoose adversary parameter auxiliary))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2) fallback)
      {coin | fullGatePrefixBad coin} output := by
  apply sourceGoodMass_congr
  · apply congrArg (fullGatePrefixSamples scalar witness parameter)
    rfl
  · rfl

set_option maxRecDepth 4096 in
/-- The original prefix good mass is the exact random-tape and tag weight sum. -/
def fullGatePrefixGood_weight_sum [fieldCert : FieldCertificate] [groupCert : GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) := by
  have expansion := fullGatePrefixGood_mass scalar witness parameter
    (prefixChoose adversary parameter auxiliary)
    (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2) fallback)
    {coin | fullGatePrefixBad coin} output
  exact (originalPrefix_eq adversary parameter auxiliary scalar witness fallback output).trans
    (expansion.trans (prefixWeight_sum_eq adversary parameter auxiliary scalar witness fallback output))

end
end Kriterion.ArgoMAC.Security
