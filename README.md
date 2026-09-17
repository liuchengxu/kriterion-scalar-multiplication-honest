# A smaller garbled circuit for fixed-scalar BN254 multiplication

**Result: `ciphertextBytes = 8,891,172`, against the 9,699,931-byte baseline — a reduction of
808,759 bytes (8.3378 %).** The scored quantity is the length of the encoding of the circuit's
declared public value, so every byte below is a byte of the published garbled circuit.

This is an **honest** construction: the evaluator never obtains the scalar. It receives 91
offset-blinded points and Horner-sums them into `s·P`; each row is 7-way ambiguous in its digit,
and recovering `s` from `s·P` is a discrete log. No simulator shortcut is used — the privacy proof
is the baseline's, carried across the change by an explicit adapter.

---

## 1. What the circuit is, and where the bytes go

The garbler holds a nonzero scalar `s`; the evaluator supplies affine coordinates. Per row `i` the
evaluator reconstructs `ρᵢ·(Oᵢ + φ^{dᵢ}(P))` from masked coefficients, and a cleartext Horner sum
cancels the offsets (`clampedFirst` forces `Σ radixⁱ·Oᵢ = 0`) to give `s·P`. The scalar is written
in radix `2 − ω` (Eisenstein norm 7), which needs **91 digits** for 254 bits.

Each row publishes, per coordinate, a handful of masked coefficients, and each coefficient's mask is
supplied by a **digit adaptor**: 254 ciphertexts, one per input bit, 32 bytes each.

```
one adaptor            = 254 × 32 B                       = 8,128 B
one row (X + Y + Z)     = 12 adaptors + 14 coefficients    ≈ 97 KB
91 rows + curve gadget                                   = 8,891,172 B
```

**99.6 % of the circuit is per-bit ciphertexts.** The input MAC is already computed once and shared
across all 91 rows; the redundancy is not there. It is in the *masks*, which must be fresh per
(row, coefficient). So the only way to shrink this circuit is to publish fewer masked coefficients,
or to make each adaptor's delivery cheaper.

## 2. Lever one: the Y row on the x-only basis (4 → 3 adaptors)

Write `n` for the masked coefficients a coordinate publishes and `J` for its adaptors. Hiding
requires

> **`n ≤ J + (values the evaluator legitimately learns)`**

because a mask must cancel the adaptor contributions **as a polynomial identity in the input** — the
table is published before the adversary chooses the input — so masks are forced affine in the
adaptors' slope and hash offsets; with `n > J + 1`, `n − J − 1` combinations of the published
coefficients are determined by the row secret alone, a checkable predicate over the 7 candidate
digits. The baseline's X row sits exactly on the boundary (`5 = 4 + 1`) and is optimal.

The Y row had one adaptor of slack: `y10` was a pure spill-canceller. On curve, `y² = x³ + 3`, so

```
c₀ + c₁x + c₄x² + c₅y²  =  (c₀ + 3c₅) + c₁x + c₄x² + c₅x³
```

and the x-only basis `{1, x, x², x³}` is **downward-closed under division by `x`** — so an adaptor
reading `x` whose spill would land on `x³`, `x²` or `x` always lands on an already-published
monomial, and no canceller is needed. Three adaptors, with slopes chosen so the chain telescopes:

```
A_a (over x, ×x²) : σ_a x³ + K_a x²      σ_a := −r₅
A_b (over x, ×x ) : σ_b x² + K_b x       σ_b := −(r₄ + K_a)
A_c (over x, ×1 ) : σ_c x  + K_c         σ_c := −(r₁ + K_b)
p₃ = k₃ + r₅   p₂ = k₂ + r₄   p₁ = k₁ + r₁   p₀ = (k₀ + 3k₅) − K_c
```

Dimensions are tight: `3 + 3·254 = 765 = (4 + 3·254) − 1`, the same shape as the X template. The
basis is well-defined **because `φ⁶ = 1`** for every digit's endomorphism (`(φ³)² = (φ⁴)³ = 1`),
which the zero digit does not violate — it maps to `none` and never reaches the basis. This is the
only row with slack; the X row is already minimal, and Z stays at 5.

**This is the optimum of the whole addition-law space, not just of RCB.** An exhaustive search over
every bidegree-(2,2) complete addition law (every `μ ∈ P²` at two primes, every `GL₃` output
mixing, every slot, plus BN254 spot-verification) shows the `y²` slot is unkillable in every row of
every representative; the only generic kill is `{y, xy}`, which is exactly this x-only row; and the
minimum is `4 + 3 + 5 = 12`. The mask-dimension law is necessary but not sufficient — the geometry
forces one canceller in every triple. So `5 + 91×12 = 1,097` adaptors is the floor of this design.

## 3. Lever two: a 254-bit payload, without touching the proof (9,625,087 on the baseline; −69,111 B on top of lever one)

`Ciphertext := BitVec 256` and `encrypt label message := padBytes label ^^^ fieldBytes message`,
where the pad is a **full 256 bits**. Since `message < p < 2^254`, the top two bits of every
ciphertext are pure pad and carry no message.

Dropping them is not free, and this is the subtle part. Two statements go **false** — not ill-typed
— if the published table is shrunk:

- `bitAdaptorGarble_eq_iff` identifies the garbler's table *plus hash lift* with exactly five
  permutation constraints; with a 254-bit row the pad fiber is 4-to-1 and the forward direction
  fails. Its consumer appears in 20 files.
- `tableBlocksEquiv` feeds `fullCircuitSource_card = |Block| ^ (5 · |RawCircuitGate|)`, the
  **denominator of the real-transcript mass**. `2^254 ≠ 2^256`.

The proof counts one published row as exactly 256 bits of oracle entropy across 301,752 gates, so
there is no local repair — the *mass* propagation is the cost.

**The resolution separates two objects that were conflated: the table the proof reasons about, and
the value that goes on the wire.** `Ciphertext`, `padBytes`, `fieldBytes`, `encrypt` and `Table`
stay at 256 bits, so all the oracle bookkeeping is untouched. The wire gets a 254-bit `Payload`; a
mirror packed public type is connected by `GarbledCircuit.mapPublic scheme pack unpack`, and the
obligations transfer through `mapPublic` — **privacy is not re-proved at all**, because both
experiments are pushed forward by the same map, preserving work and advantage. The entire cost of
the construction change on the existing proof is **one declaration** (`padGate_evaluate_of_matches`).

Each adaptor packs to `254 × 254 bits = 64,516 bits → 8,065 B` against 8,128 B = **−63 B**, times
1,097 adaptors = **−69,111 B**.

## 4. What is deliberately left on the table

- **867 B**: 548 B of per-adaptor rounding (4 spare bits each — `Encoding` forces byte-aligned
  components, so joint packing costs legibility) plus 319 B of unpacked coefficients.
- **3,003 B** of `Option` tags (11 per row-coordinate × 3 × 91), of which 637 B is paid for absent
  fields no evaluator ever reads. Row identity is statically known, so a row-shaped public table
  would reclaim all of it.

Both are shape changes to the encoded public value at the cost of legibility, and neither is worth
the risk at 0.04 % combined.

## 5. Honest disclosure

- **The scalar is not disclosed.** The evaluator obtains `s·P`; recovering `s` needs a discrete log.
  The 91 rows are information-theoretically 7-way ambiguous in their digits.
- **No simulator shortcut.** The simulator is the baseline's; `mapPublic` transfers it rather than
  replacing it. There is no `Classical.choose`-based discrete log and no conditional disclosure.
- **The metric is the encoding's, and the encoding is the construction's choice** — that is the
  challenge's rule (`ciphertextSize` requires only that the declared count *equal* the encoding
  length). The packing above is ordinary bit-packing of a value the evaluator can decode exactly,
  not a relocation of payload into the Lamport labels, which the challenge forbids and which this
  construction does not do: the labels remain exactly the 508 selected blocks.

## 6. Verification

Checked locally with the platform's own `verifier.mjs` — the same five gates it runs:

```json
{"checks": {"layout":"pass","build":"pass","obligation":"pass",
            "axioms":{"result":"pass","list":["propext","Classical.choice","Quot.sound"]},
            "lint":"pass"},
 "metrics": {"ciphertext_bytes": 8891172},
 "diagnostic": null}
```

`#print axioms Submission.solution` → `{propext, Classical.choice, Quot.sound}`. No `sorry`, no
`axiom`, no `native_decide`, no `implemented_by`, no `extern`. The single `noncomputable` is
`Simulator.mapPublic`, mirroring the baseline's own `noncomputable Simulator.mapLabels`, and it lives
under `Proof/`, not `Construction/`.

Every step was reviewed by an independent lane that was told to distrust the reports it was handed,
and several of those reviews overturned claims made during the work — including two of the author's
own designs (`B′` and option `A`), one prescribed proof lemma that was provable but unusable, and a
"leaf lemma" whose single misjudged member turned out to be the bridge into the mass accounting.

## 7. Provenance

Derived from the `argomac-lean` baseline (`711689cd`) and the challenge library
(`bn254-scalar-multiplication/formal`, 14/14 files byte-identical to the reference). The full cost
model — the mask-dimension law, the spill-routing rule, the eleven closed doors, and the
addition-law search that fixes the floor at 12 adaptors per row — is documented alongside the
implementation; the design space is written down there rather than here so that this file stays a
description of the artifact.
