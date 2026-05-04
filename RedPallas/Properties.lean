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

/-! ## Key homomorphism

`keygen` is a group homomorphism from `(Fq, +)` to `(Pallas, +)`.
This is the algebraic foundation for Zcash's value commitment scheme:
the binding verification key `bvk = Σ cvᵢ` works because summing
commitments corresponds to summing their secret keys. -/

/-- **Key homomorphism**: `keygen` distributes over addition.

`keygen(a + b) = keygen(a) + keygen(b)` -/
theorem keygen_add (a b : Pasta.Fq) :
    keygen (a + b) = keygen a + keygen b := by
  unfold keygen; rw [fqSmul_add]

/-- **Key negation**: `keygen` commutes with negation.

`keygen(-sk) = -keygen(sk)` -/
theorem keygen_neg (sk : Pasta.Fq) :
    keygen (-sk) = -keygen sk := by
  unfold keygen; rw [fqSmul_neg]

/-- **Key subtraction**: `keygen` distributes over subtraction.

`keygen(a - b) = keygen(a) - keygen(b)` -/
theorem keygen_sub (a b : Pasta.Fq) :
    keygen (a - b) = keygen a - keygen b := by
  unfold keygen; rw [fqSmul_sub]

/-- `keygen` respects scalar multiplication: `keygen(a·b) = a ⬝ keygen(b)`.

This is the module homomorphism property of key generation: scaling the secret
key by a scalar `a` is the same as scalar-multiplying the public key by `a`.
Used when composing key derivation paths. -/
theorem keygen_mul (a b : Pasta.Fq) : keygen (a * b) = fqSmul a (keygen b) := by
  unfold keygen; exact fqSmul_mul a b G

/-- `keygen(0)` is the identity point. -/
@[simp]
theorem keygen_zero : keygen 0 = (0 : Pallas.toAffine.Point) := by
  unfold keygen; simp

/-! ## Signature negation

Negating the scalar component of a signature corresponds to negating the
verification key. -/

/-- Negating a signature's scalar negates the verification key relationship.

If `[S]·G = R + [c]·vk`, then `[-S]·G = -(R + [c]·vk)`, not `R + [c]·(-vk)`,
because the challenge `c` depends on `vk`. However, negation IS involutive. -/
@[simp]
theorem negateS_negateS (sig : Signature) :
    negateS (negateS sig) = sig := by
  simp [negateS]

/-! ## Generic verification (BindingSig)

The verification equation `[S]·G = R + [c]·vk` holds purely by linearity
of Fq-scalar multiplication, independent of which generator is used.
This means `BindingSig` inherits the same correctness guarantees as
`SpendAuthSig`. -/

/-- **Generic verification correctness**: the RedDSA verification equation
holds for any generator point.

This covers both `SpendAuthSig` (generator `G`) and `BindingSig`
(generator `BindingG`). -/
theorem verify_sign_generic (gen : Pallas.toAffine.Point)
    (sk : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) :
    let vk := sk ⬝ gen
    let R := r ⬝ gen
    let c := challengeHash R vk msg
    (r + c * sk) ⬝ gen = R + c ⬝ vk := by
  simp only []
  rw [fqSmul_add, fqSmul_mul]

end

end RedPallas
