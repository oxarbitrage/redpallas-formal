import RedPallas.Spec

namespace RedPallas

/-! # Security properties of RedPallas

The key algebraic properties of the RedPallas signature scheme:

1. **Verification correctness**: honestly generated signatures always verify.
2. **Re-randomization consistency**: re-randomizing the key pair preserves
   the key generation relationship.
3. **Re-randomized verification**: signing with a re-randomized key produces
   signatures that verify against the re-randomized public key.

These properties rely on the linearity of Fq-scalar multiplication over
the Pallas group.

See §5.4.7 of the Zcash protocol specification.
-/

open Pasta

noncomputable section

/-- **Verification correctness**: a signature produced by `sign` always
passes `verify` with the corresponding public key.

Proof: `[S]·G = [r + c·sk]·G = [r]·G + [c·sk]·G = R + [c]·([sk]·G) = R + [c]·vk`. -/
theorem verify_sign (sk : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) :
    verify (keygen sk) msg (sign sk msg r) := by
  unfold verify sign keygen
  simp only []
  rw [fqSmul_add, fqSmul_mul]

/-- **Re-randomization consistency**: re-randomizing the secret key and
computing the public key gives the same result as re-randomizing the
public key directly.

`[sk + α]·G = [sk]·G + [α]·G = vk + [α]·G` -/
theorem rerandomize_keygen (sk α : Pasta.Fq) :
    keygen (rerandomizeSk α sk) = rerandomizeKey α (keygen sk) := by
  unfold keygen rerandomizeSk rerandomizeKey
  rw [fqSmul_add]

/-- **Re-randomized verification**: signing with a re-randomized secret key
produces a valid signature under the re-randomized public key.

This is the core property enabling Zcash's spend authorization: the prover
re-randomizes their key pair with `α`, signs with `rsk = sk + α`, and the
verifier checks against `rk = vk + [α]·G`. -/
theorem verify_rerandomized (sk α : Pasta.Fq) (msg : List UInt8)
    (r : Pasta.Fq) :
    verify (rerandomizeKey α (keygen sk)) msg
      (sign (rerandomizeSk α sk) msg r) := by
  rw [← rerandomize_keygen]
  exact verify_sign (rerandomizeSk α sk) msg r

end

end RedPallas
