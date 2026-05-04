# redpallas-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of the RedPallas signature scheme (RedDSA over Pallas) used for spend authorization and value binding in Zcash's Orchard protocol.

## What's formalized

- **`verify_sign`** — honest signatures always verify: [r + c·sk]·G = R + [c]·vk.
- **`verify_rerandomized`** — signing with sk+α verifies against vk+[α]·G.
- **`keygen_add`** — key generation is a group homomorphism: keygen(a+b) = keygen(a) + keygen(b).

Unforgeability (EUF-CMA) is **not** formalized — it requires a random oracle model not yet in Lean/Mathlib.

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
