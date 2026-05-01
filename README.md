# redpallas-formal

Lean 4 formalization of the [RedPallas](https://zips.z.cash/protocol/protocol.pdf) signature scheme used in Zcash's [Orchard](https://zcash.github.io/orchard/) protocol.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `RedPallas` namespace. Built on top of [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

| Component | File | Description |
|-----------|------|-------------|
| Group order (axiom) | `RedPallas/ScalarMul.lean` | Pallas group has order `Fq.p`, axiomatized |
| Fq-scalar multiplication | `RedPallas/ScalarMul.lean` | `s ⬝ P = [s.val]·P` with linearity proofs |
| nsmul mod order | `RedPallas/ScalarMul.lean` | `(m % q)·P = m·P` — reduction modulo group order |
| fqSmul linearity | `RedPallas/ScalarMul.lean` | Distributivity over addition and compatibility with multiplication |
| fqSmul negation | `RedPallas/ScalarMul.lean` | `(-s) ⬝ P = -(s ⬝ P)` and subtraction |
| Challenge hash (opaque) | `RedPallas/Spec.lean` | `H(R, vk, msg) → Fq`, axiomatized |
| Generator G (opaque) | `RedPallas/Spec.lean` | Fixed generator with non-identity proof |
| Key generation | `RedPallas/Spec.lean` | `vk = [sk]·G` |
| Signature type | `RedPallas/Spec.lean` | `(R, S)` commitment-response pair |
| Sign | `RedPallas/Spec.lean` | `R = [r]·G`, `S = r + c·sk` |
| Verify | `RedPallas/Spec.lean` | `[S]·G = R + [c]·vk` |
| Re-randomize key | `RedPallas/Spec.lean` | `rk = vk + [α]·G` |
| Re-randomize secret | `RedPallas/Spec.lean` | `rsk = sk + α` |
| Signature negation | `RedPallas/Spec.lean` | `negateS(R, S) = (R, -S)` with involution proof |
| BindingG (opaque) | `RedPallas/Spec.lean` | Binding signature generator, distinct from `G` |
| **Verification correctness** | `RedPallas/Properties.lean` | Honestly generated signatures always verify |
| **Re-randomization consistency** | `RedPallas/Properties.lean` | `keygen(sk + α) = keygen(sk) + [α]·G` |
| **Re-randomized verification** | `RedPallas/Properties.lean` | Signing with re-randomized key verifies against re-randomized public key |
| **Key homomorphism** | `RedPallas/Properties.lean` | `keygen(a + b) = keygen(a) + keygen(b)`, plus negation and subtraction |
| **Generic verification** | `RedPallas/Properties.lean` | Verification equation holds for any generator (covers both SpendAuth and Binding) |

## Security argument

RedPallas is an instantiation of RedDSA (§5.4.7 of the Zcash protocol spec) over the Pallas curve:

1. **Verification correctness** (proven): `[r + c·sk]·G = [r]·G + [c]·([sk]·G)` by linearity of scalar multiplication.
2. **Re-randomization** (proven): key re-randomization preserves the keygen relationship and signature validity, enabling Zcash's spend authorization privacy.
3. **Key homomorphism** (proven): `keygen` is a group homomorphism from `(Fq, +)` to `(Pallas, +)`, supporting value commitment balancing.
4. **Generic verification** (proven): the verification equation holds for any generator, covering both SpendAuthSig and BindingSig.
5. **Unforgeability**: reduces to the discrete logarithm problem on Pallas (not formalized — requires modeling the random oracle).

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build     # builds in ~10 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve library, group law, tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas/Vesta curve definitions and primality proofs

## References

- [Zcash protocol specification, §5.4.7](https://zips.z.cash/protocol/protocol.pdf) — RedDSA/RedPallas specification
- [zcash/orchard](https://github.com/zcash/orchard) — Rust implementation
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization
- [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) — Sinsemilla hash Lean 4 formalization
