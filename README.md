# redpallas-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of the RedPallas signature scheme (RedDSA over Pallas) used for spend authorization and value binding in Zcash's Orchard protocol.

## What's formalized

- **`verify_sign`** — honest signatures always verify: [r + c·sk]·G = R + [c]·vk.
- **`verify_rerandomized`** — signing with sk+α verifies against vk+[α]·G.
- **`keygen_add`** — key generation is a group homomorphism: keygen(a+b) = keygen(a) + keygen(b).
- **`two_fork_extract`** — Schnorr two-fork key extraction: from two valid transcripts with the same commitment but different challenges, extract the discrete log of the verification key.
- **`binding_extractability`** — specialization to BindingSig: extracts `bsk` such that `bvk = [bsk]·BindingG`, matching the shape of [Ironwood](https://github.com/zcash/ironwood)'s `hExtract` hypothesis.

Unforgeability (EUF-CMA) is **not** formalized — it requires a random oracle model not yet in Lean/Mathlib. The extractability theorems above prove the algebraic core; the forking lemma (Pointcheval–Stern) that produces the two transcripts in the ROM is not yet formalized.

## Axioms

| Axiom | Justification |
|-------|--------------|
| `order_pallas` | \|Pallas(𝔽_p)\| = q — same gap as `cycle_conjecture_pallas` in [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| `challengeHash` | BLAKE2b-based hash, opaque by design |
| `G_ne_zero`, `BindingG_ne_zero` | Certified Zcash parameters |

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4), [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

## References

- [Zcash Protocol Spec §5.4.6](https://zips.z.cash/protocol/protocol.pdf) — RedDSA
- [ZIP-215](https://zips.z.cash/zip-0215)

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
