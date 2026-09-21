# Where the 9 % comes from

This document explains the theory behind the size reduction and then **attributes every byte to the exact
source change that produced it**, with the evidence — so that each number can be checked rather than taken on
trust. `README.md` describes the artifact; this file is the accounting behind it.

---

## 1. The cost identity

The garbler holds a secret scalar. What it publishes is a table of rows, each computing a polynomial in the
input coordinates `(x, y)`. Every published coefficient is **masked** — a random-looking value is added so the
real coefficient cannot be read — and each mask is delivered as a **digit adaptor**: 254 ciphertexts, one per
bit of the input, 32 bytes each.

```
one digit adaptor   = 254 × 32 B          = 8,128 B     (one per input bit)
one row             = 12 adaptors + 14 coefficients
                      + presence tags
```

**A row publishes 12 adaptors and 14 coefficients**, and those two counts are deliberately stated separately
because they are *not* the same number. The X coordinate publishes 5 coefficients on 4 adaptors: one
coefficient's mask is absorbed into the published constant rather than given its own adaptor. So the
per-coefficient cost is a *bound*, not an identity:

```
masks needed  ≤  published coefficients − (values the evaluator legitimately learns)
```

This document uses **"mask" and "adaptor" interchangeably** and always counts adaptors, never coefficients.

The consequence that matters: **99.6 % of the circuit is adaptor ciphertexts.** The input MAC is already
computed once and shared across all rows, so the redundancy is not there. It is in the masks, which must be
fresh per (row, coefficient).

```
91 rows × 12 adaptors × 8,128 B   ≈  8.9 MB      ← the whole object
```

---

## 2. The levers

### Lever A — the Y row's canceller adaptor: **−739,648 B**

A mask's hash spill must land on a **monomial the row already publishes**. If it would land on a monomial the
row does not publish, a second adaptor is needed whose only job is to cancel it.

The Y row before this work published `{1, x, x², y²}` and used **four** adaptors:

```lean
-- rebase/entry/Construction/ArgoMAC/Biquadratic.lean:106   (the revision-15 baseline)
let y8  := DigitAdaptor.garble oracles.y8  (-randomness.r5) inputKey.y
let y10 := DigitAdaptor.garble oracles.y10 (-r8)            inputKey.y
```

`y10` is that second adaptor, and the mechanism is exact: the quadratic coefficient is masked as
`(c₅ + r₅)y²`, the `y8` adaptor contributes `(−r₅y + r₈)y`, and their sum therefore leaves an unwanted
**linear `r₈y`** term. The Y table publishes no linear-`y` coefficient (`c2 := none`), so there is nothing to
absorb it. `y10` supplies `−r₈y + r₁₀`, and the published constant subtracts `r₁₀`.

**The change.** On the curve `y² = x³ + 3`, so `c₅y² = c₅x³ + 3c₅`. The row is rewritten in the x-only cubic
basis `{1, x, x², x³}`:

```
c₀ + c₁x + c₄x² + c₅y²  =  (c₀ + 3c₅) + c₁x + c₄x² + c₅x³
```

All three adaptors now read `x`, with multipliers `x²`, `x`, `1`, and every spill lands on `x³`, `x²` or `x` —
all published. The chain absorbs everything, so no *extra canceller-only* adaptor is needed.

Two precisions, both of which correct an earlier telling of this story:

- **Cancellation still happens.** Cancelling is what masking *is*; the arithmetic throughout the three-adaptor
  chain is a chain of cancellations. What disappears is specifically the spill into a monomial slot the row
  does not publish.
- **The closure is a polynomial identity**, and does not require division by `x`. So `x = 0` is not an
  exception, and the zero digit is covered by the same argument.

| | adaptors in the Y row |
|---|---|
| baseline | **4** — `y8`, `y10`, `x7`, `x9` |
| ours | **3** — `y6`, `x7`, `x9`, all reading `x` |

Sources: `rebase/entry/Construction/ArgoMAC/Biquadratic.lean` (`garbleY`, 4 adaptors) against
`rebase2/entry/Construction/ArgoMAC/Biquadratic.lean` (`garbleY`, 3; the rebound polynomial at
`FieldMacToECMac.lean:169-172`).

**Arithmetic.** One adaptor removed on each of 91 rows, at the *unpacked* size — the deletion is attributed
before the packing lever, for the reason in §3:

```
91 × 8,128 = 739,648 B
```

**Evidence.** `Wire.yRow_length` is **32,651** before and **24,322** after (below), and the tree compiles at
the new value, so the row genuinely shrank by one adaptor rather than by re-encoding.

---

### Lever B — the 92nd row: **−106,145 B**

The scalar is written in a number system (radix `2 − ω`) whose expansion needs about 91 digits. The
revision-15 baseline selects **one fixed initial state** and needs **92**:

```lean
-- rebase/entry/Construction/ArgoMAC/Base7.lean:268
terminal : ∀ scalar, after 92 (glvInitial scalar) = ⟨0, 0⟩
```

The tree also contains a **four-corner selection**: `shortInitial` tries four shifted initial states and takes
one that terminates in **91** steps — and that is a **theorem**, not a hypothesis:

```lean
-- rebase2/entry/Proof/Correctness/Base7Termination.lean:678
theorem shortInitialTerminates91 (scalar : BN254.ScalarField) :
    after 91 (shortInitial scalar) = ⟨0, 0⟩
```

It is an unconditional, all-scalar proof: a geometric covering argument establishes that one of the four
candidates has small Eisenstein norm (`existsCandidateNormBound`, for *every* `k`), then an induction on the
norm gives termination. It is **not** a test over sampled scalars, and the suspicious-looking `else state₃` in
`shortInitial`'s definition **is genuinely justified** — if candidates 0, 1 and 2 fail, existence supplies a
terminating candidate, and the four-way membership split leaves candidate 3.

**The change.** Use `shortInitial` with 91 digits.

| | value |
|---|---|
| `FieldMacToECMac.outputMacCount` | **92** → **91** |
| certificate | `after 92 (glvInitial …)` → `after 91 (shortInitial …)` |
| `Construction.digits` | `decompose 92 (glvInitial …)` → `decompose 91 (shortInitial …)` |

**Arithmetic.** One row at the *baseline* row size, because a row is removed before its successor rows are
re-encoded:

```
106,145 B  = one baseline row
```

**What this is *not*.** The 92nd row is **not** a zero or dummy row. It can carry a real, nonzero digit — under
the baseline's own definitions there are scalars whose 92nd digit is `negOmegaSquared`. The saving comes from a
different initial-state *algorithm*, not from deleting padding. (An earlier telling of this document said
otherwise; it was wrong.)

**Stronger? No — smaller.** Both certificates are abstract hypotheses at their generic use sites, and **both
have proved instances**: the baseline discharges `glvInitialTerminates92` from a real norm-bound proof. We are
not stronger because the baseline lacked a proof; we use fewer rows with a different selection.

---

### Lever C — the payload is 254 bits, not 256: **−69,111 B**

A ciphertext is `padBytes ⊕ fieldBytes message`, where `padBytes` is a full 256 bits. The BN254 base field
modulus lies strictly between `2^253` and `2^254` (`formal/BN254.lean:17-18`), so `fieldBytes` zeroes the top
two bits of every message:

```
Ciphertext = padBytes(256 bits) ⊕ message(< 2^254)     → the top 2 bits are pure pad
```

Dropping them is **lossless**, provided the mask is projected too: `decrypt` XORs the projected pad, not a
truncated ciphertext against a full-width pad (`BitAdaptor.lean:64-75`). The proof uses `message.val_lt` and
the modulus bound, and `Packed.lean`'s `evaluate_unpack_pack` proves evaluation is unchanged by the round trip.

**Arithmetic.** 63 bytes saved on every adaptor, over the whole circuit:

```
254 × 254 bits = 64,516 bits = 8,065 B   vs   8,128 B   →  −63 B each
(5 + 91 × 12) × 63 = 1,097 × 63          =  −69,111 B
```

---

### Lever D — tags and coefficient packing: **−3,276 B**

Two smaller savings in the same encoding change:

| | bytes |
|---|---|
| **presence tags** — the row shape is statically fixed, so `Option` presence carries nothing — 11 tags × 3 row-coordinates × 91 rows | **−3,003** |
| **coefficient packing** — 5/4/5 coefficients at 32 B each become 159/127/159 B (254 bits each), so 1 byte per group × 3 groups × 91 rows | **−273** |

The curve gadget's coefficient group stays at 96 bytes and saves nothing, and it carries no tags.

---

## 3. The telescoping

```
  9,806,076   revision-15 baseline (argomac-lean@6796e286)
−   106,145   Lever B — one fewer row (92 → 91)
−   739,648   Lever A — the Y canceller adaptor, at unpacked size (91 × 8,128)
−    69,111   Lever C — packing adaptor payloads to 254 bits (1,097 × 63)
−     3,003   Lever D — presence tags (91 × 3 × 11)
−       273   Lever D — coefficient packing (91 × 3)
= 8,887,896   ✓   −918,180 B, −9.363 %
```

**Which baseline you compare against changes the story, and it is worth being explicit about it.**

| comparison | total | levers |
|---|---|---|
| vs the **pre-revision** baseline (9,699,931) | −812,035 B, −8.372 % | A, C, D only — that baseline already used 91 rows, so Lever B does not exist there |
| vs the **revision-15** baseline (9,806,076) | −918,180 B, −9.363 % | A, B, C, D |

The 106,145-byte difference between the two baselines is the revision-15 baseline's *own* extra row, which
Lever B recovers.

**The A/C split is ordering-dependent.** Deletion and packing interact: a row deleted *before* packing saves
8,128 B, and one deleted *after* would have saved 8,065 B. Taking packing first would attribute
`91 × 8,065 = 733,915` to deletion and a further `91 × 63 = 5,733` to packing. Neither attribution is uniquely
intrinsic; the ordering above is stated so the published 739,648 is reproducible and checkable.

---

## 4. What is not claimed

- **This is not a general lower bound.** Counting *this* construction's adaptors does not prove that no
  construction does better. The lever-A optimum (12 adaptors per row) was established by an exhaustive search
  of the bidegree-(2,2) complete addition law space, which is a statement about *that* space.
- **The row's basis, not the arithmetic, is the lever.** A row's monomial basis decides how many masks it
  needs, because it decides where a mask's spill lands. That is the transferable idea; the specific x-only
  cubic basis is one instance of it.
- **Lever B replaces one initial-state selection with another.** It does not establish that 91 is minimal, only
  that 91 suffices and is proved. Whether the organizer chose 92 for a reason the source does not record is
  **not settled** — `shortInitial` also performs data-dependent candidate checks, which is a garbler-side cost.
- **The packing is a relabelling, not a reduction of the garbling.** The proof's oracle-entropy object stays
  256 bits; only the transmitted value shrinks. That is why privacy did not have to be re-proved.
- **Both termination certificates are proved.** Where this document says the baseline "assumes" the 92-round
  property, it means the certificate is a typeclass hypothesis at its generic use site — the same structure
  ours has. It is discharged by a proof in both trees.
