# redpallas-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of the RedPallas signature scheme (a RedDSA instantiation over the Pallas curve) used for spend authorization and value binding in Zcash's Orchard protocol.

## Overview

RedPallas = RedDSA over Pallas. Orchard uses it for two distinct purposes:

- **SpendAuthSig** — authorizes the spending of a note. The prover holds a spending key `sk` and produces a Schnorr signature using generator `G`.
- **BindingSig** — proves that value is balanced across a transaction (i.e., the sum of input values equals the sum of output values plus the net value). It uses a separate generator `BindingG` tied to value commitment randomness.

**Re-randomization** is essential for privacy. Without it, the verifier could link different spends to the same spending key by comparing public keys. Re-randomization works by replacing `(sk, vk)` with `(sk + α, vk + [α]·G)` for a fresh random scalar `α`. Because `[α]·G` is computationally indistinguishable from a fresh group element (under DLP), the re-randomized key is unlinkable to the original. The key homomorphism `keygen(sk + α) = keygen(sk) + [α]·G` ensures that a signature produced with `sk + α` verifies correctly against `vk + [α]·G`.

## Mathematical Background

### RedDSA over Pallas

RedDSA (§5.4.6 of the Zcash protocol specification) is a re-randomizable Schnorr signature scheme. The RedPallas instantiation uses the Pallas elliptic curve, with scalar field `Fq` (of prime order `Fq.p`).

**Key generation:** Given a secret key `sk ∈ Fq`, the verification key is `vk = [sk]·G`.

**Signing:** Given `sk`, message `msg`, and nonce `r ∈ Fq`:
1. Compute `R = [r]·G`
2. Compute challenge `c = H(R, vk, msg)` (BLAKE2b-based hash into `Fq`)
3. Output signature `(R, S)` where `S = r + c·sk`

**Verification:** Given `vk`, `msg`, and signature `(R, S)`:
1. Recompute `c = H(R, vk, msg)`
2. Accept iff `[S]·G = R + [c]·vk`

The equation holds because:
```
[S]·G = [r + c·sk]·G = [r]·G + [c·sk]·G = R + [c]·([sk]·G) = R + [c]·vk
```
This is a direct consequence of the distributivity of scalar multiplication (`fqSmul_add`, `fqSmul_mul`).

### Re-Randomization

Given a re-randomization scalar `α ∈ Fq`:
- **Re-randomized verification key:** `rerandomizeKey(α, vk) = vk + [α]·G`
- **Re-randomized signing key:** `rerandomizeSk(α, sk) = sk + α`

The fundamental **key homomorphism property** states:
```
keygen(sk + α) = [sk + α]·G = [sk]·G + [α]·G = vk + [α]·G = rerandomizeKey(α, vk)
```
This means signing with `rsk = sk + α` produces signatures that verify against `rk = vk + [α]·G`, with no extra effort — it reduces directly to `verify_sign` applied to `rsk`. The re-randomized key is computationally indistinguishable from a freshly generated key, providing unlinkability between spends.

### What Is NOT Formalized

**Unforgeability (EUF-CMA) is not proven.** Proving it would require:
1. Modeling `H` as a random oracle (ROM framework)
2. Showing that any polynomial-time adversary capable of forging a signature can be used to solve the discrete logarithm problem on Pallas

The ROM framework is not yet available in Lean/Mathlib. The proofs here are purely algebraic: they establish correctness (honest signatures verify) but make no claim about the hardness of breaking the scheme. The security reduction is standard and documented in the Zcash protocol specification.

## Formalization

### `RedPallas/ScalarMul.lean`

Defines `fqSmul (s : Fq) (P : Pallas.Point) : Pallas.Point` (notation `s ⬝ P`) as `s.val • P` — scalar multiplication by the natural number representative of `s`, reduced modulo the group order. The key bridge lemma is `nsmul_mod_order`, which shows `(m % Fq.p) • P = m • P` using `order_pallas`.

The linear algebra package proved here:

| Lemma | Statement |
|-------|-----------|
| `fqSmul_def` | `s ⬝ P = s.val • P` (simp lemma) |
| `nsmul_mod_order` | `(m % Fq.p) • P = m • P` |
| `fqSmul_add` | `(a + b) ⬝ P = a ⬝ P + b ⬝ P` |
| `fqSmul_mul` | `(a * b) ⬝ P = a ⬝ (b ⬝ P)` |
| `fqSmul_add_right` | `s ⬝ (P + Q) = s ⬝ P + s ⬝ Q` |
| `fqSmul_zero` | `(0 : Fq) ⬝ P = 0` |
| `fqSmul_one` | `(1 : Fq) ⬝ P = P` |
| `fqSmul_neg` | `(-s) ⬝ P = -(s ⬝ P)` |
| `fqSmul_sub` | `(a - b) ⬝ P = a ⬝ P - b ⬝ P` |

### `RedPallas/Spec.lean`

Defines the RedPallas algorithms and their two generators as axioms:

**Axioms:**
- `challengeHash : Pallas.Point → Pallas.Point → List UInt8 → Fq` — opaque hash function (BLAKE2b-based in practice)
- `G : Pallas.Point` — SpendAuthSig generator
- `G_ne_zero : G ≠ 0`
- `BindingG : Pallas.Point` — BindingSig generator (value commitment randomness base)
- `BindingG_ne_zero : BindingG ≠ 0`

**Definitions:**
- `keygen (sk : Fq) : Pallas.Point` — `sk ⬝ G`
- `Signature` — structure `{ R : Pallas.Point, S : Fq }`
- `sign (sk : Fq) (msg : List UInt8) (r : Fq) : Signature` — `⟨r ⬝ G, r + challengeHash (r ⬝ G) (keygen sk) msg * sk⟩`
- `verify (vk : Pallas.Point) (msg : List UInt8) (sig : Signature) : Prop` — `sig.S ⬝ G = sig.R + (challengeHash sig.R vk msg) ⬝ vk`
- `rerandomizeKey (α : Fq) (vk : Pallas.Point) : Pallas.Point` — `vk + α ⬝ G`
- `rerandomizeSk (α : Fq) (sk : Fq) : Fq` — `sk + α`
- `negateS (sig : Signature) : Signature` — `⟨sig.R, -sig.S⟩`

### `RedPallas/Properties.lean`

All proven theorems, with no `sorry`:

| Theorem | Statement |
|---------|-----------|
| `verify_sign` | `verify (keygen sk) msg (sign sk msg r)` |
| `rerandomize_keygen` | `keygen (rerandomizeSk α sk) = rerandomizeKey α (keygen sk)` |
| `verify_rerandomized` | `verify (rerandomizeKey α (keygen sk)) msg (sign (rerandomizeSk α sk) msg r)` |
| `keygen_add` | `keygen (a + b) = keygen a + keygen b` |
| `keygen_neg` | `keygen (-sk) = -keygen sk` |
| `keygen_sub` | `keygen (a - b) = keygen a - keygen b` |
| `keygen_zero` | `keygen 0 = (0 : Pallas.Point)` |
| `negateS_negateS` | `negateS (negateS sig) = sig` |
| `verify_sign_generic` | For any generator `gen`, `(r + c * sk) ⬝ gen = r ⬝ gen + c ⬝ (sk ⬝ gen)` |

## Key Results

### Theorem: Signature Correctness (`verify_sign`)

```lean
theorem verify_sign (sk : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) :
    verify (keygen sk) msg (sign sk msg r)
```

For any secret key `sk`, message `msg`, and nonce `r`, the signature produced by `sign` passes `verify` with the corresponding public key `keygen sk`.

**Proof sketch:** Unfold the definitions; the goal reduces to showing
```
(r + c * sk) ⬝ G = r ⬝ G + c ⬝ (sk ⬝ G)
```
which follows immediately from `fqSmul_add` (scalar addition distributes over the group) and `fqSmul_mul` (scalar multiplication associates).

### Theorem: Re-Randomization Correctness (`verify_rerandomized`)

```lean
theorem verify_rerandomized (sk α : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) :
    verify (rerandomizeKey α (keygen sk)) msg (sign (rerandomizeSk α sk) msg r)
```

Signing with `rsk = sk + α` and verifying against `rk = vk + [α]·G` succeeds. This is Orchard's spend authorization mechanism in a nutshell.

**Proof:** By `rerandomize_keygen`, `keygen (sk + α) = vk + [α]·G`, so the re-randomized public key equals `keygen (rerandomizeSk α sk)`. The result then follows directly from `verify_sign` applied to `rerandomizeSk α sk`.

### Theorem: Key Homomorphism (`keygen_add`)

```lean
theorem keygen_add (a b : Pasta.Fq) :
    keygen (a + b) = keygen a + keygen b
```

`keygen` is a group homomorphism from `(Fq, +)` to `(Pallas, +)`. Together with `keygen_neg`, `keygen_sub`, and `keygen_zero`, this establishes that `keygen` is a homomorphism of abelian groups. This is the algebraic foundation for BindingSig: the binding verification key `bvk = Σᵢ cvᵢ` (sum of value commitments) corresponds to `keygen(Σᵢ skᵢ)`, allowing the verifier to check balance without learning individual keys.

### Theorem: Generic Verification (`verify_sign_generic`)

```lean
theorem verify_sign_generic (gen : Pallas.toAffine.Point)
    (sk : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) :
    let vk := sk ⬝ gen
    let R  := r ⬝ gen
    let c  := challengeHash R vk msg
    (r + c * sk) ⬝ gen = R + c ⬝ vk
```

The verification equation holds for **any** generator point, not just `G`. This one theorem covers both `SpendAuthSig` (generator `G`) and `BindingSig` (generator `BindingG`), showing the correctness argument is purely algebraic and generator-agnostic.

## Axioms

| Axiom | File | Justification |
|-------|------|---------------|
| `order_pallas` | `ScalarMul.lean` | `\|Pallas(Fp)\| = Fq.p` — requires Schoof's point-counting algorithm; left as future work in [pasta-formal](https://github.com/oxarbitrage/pasta-formal) (`cycle_conjecture_pallas`) |
| `challengeHash` | `Spec.lean` | BLAKE2b-based hash into `Fq`; opaque by design — its internal structure is irrelevant to the algebraic proofs |
| `G_ne_zero` | `Spec.lean` | SpendAuthSig generator is a non-identity point — a certified parameter of the Orchard protocol |
| `BindingG_ne_zero` | `Spec.lean` | BindingSig generator is a non-identity point — same justification |

**Note on `order_pallas`:** This axiom asserts that the Pallas group has prime order `Fq.p`. It is the same result stated as a conjecture (`cycle_conjecture_pallas`) in [pasta-formal](https://github.com/oxarbitrage/pasta-formal). Proving it requires Schoof's algorithm for counting points on elliptic curves over finite fields, which is not yet available in Mathlib. All other results in this library are unconditionally proven modulo this one axiom (and the three opaque-by-design axioms above).

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve group law, `ZMod`, `nsmul`, ring and group tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas curve (`Pasta.Pallas`), scalar fields `Fp` and `Fq`, and their primality proofs

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is pinned in `lean-toolchain` and installed automatically.

```shell
lake update   # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build
```

## References

- [Zcash Protocol Specification §5.4.6](https://zips.z.cash/protocol/protocol.pdf) — RedDSA algorithm
- [Zcash Protocol Specification §4.2](https://zips.z.cash/protocol/protocol.pdf) — Orchard Spend Authorization
- [ZIP 215](https://zips.z.cash/zip-0215) — RedDSA / RedPallas specification
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta curve formalization; home of the open `cycle_conjecture_pallas`
- [zcash/orchard](https://github.com/zcash/orchard) — reference Rust implementation

## License

MIT
