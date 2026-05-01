import RedPallas.ScalarMul

namespace RedPallas

/-! # RedPallas signature scheme specification

RedPallas is a re-randomizable Schnorr signature scheme over the Pallas curve,
used in Zcash's Orchard protocol for spend authorization (`SpendAuthSig`).

It is an instantiation of RedDSA (§5.4.7 of the Zcash protocol specification)
with the Pallas curve as the group.

## Algorithm

- **KeyGen**: `sk ∈ Fq`, `vk = [sk]·G`
- **Sign(sk, msg, r)**: `R = [r]·G`, `c = H(R, vk, msg)`, `S = r + c·sk`
- **Verify(vk, msg, (R, S))**: check `[S]·G = R + [c]·vk`
- **Re-randomize**: `rk = vk + [α]·G`, `rsk = sk + α`
-/

open Pasta

noncomputable section

/-- The challenge hash function, mapping `(R, vk, msg)` to a scalar in `Fq`.

In practice this is a BLAKE2b-based hash. We axiomatize it as an opaque
function since its internal structure is not needed for the algebraic
security properties. -/
axiom challengeHash :
    Pallas.toAffine.Point → Pallas.toAffine.Point → List UInt8 → Pasta.Fq

/-- The generator point `G` for RedPallas (SpendAuthSig).

In practice this is a fixed generator of the Pallas group. -/
axiom G : Pallas.toAffine.Point

/-- The generator is not the identity point. -/
axiom G_ne_zero : G ≠ 0

/-- Generate a public key from a secret key: `vk = [sk]·G`. -/
def keygen (sk : Pasta.Fq) : Pallas.toAffine.Point := sk ⬝ G

/-- A RedPallas signature consists of a commitment point `R` and a
scalar response `S`. -/
structure Signature where
  R : Pallas.toAffine.Point
  S : Pasta.Fq

/-- Create a signature: `R = [r]·G`, `S = r + c·sk` where `c = H(R, vk, msg)`.

The nonce `r` is a parameter; in practice it is derived deterministically
from a random seed, the secret key, and the message. -/
def sign (sk : Pasta.Fq) (msg : List UInt8) (r : Pasta.Fq) : Signature :=
  let vk := keygen sk
  let R := r ⬝ G
  let c := challengeHash R vk msg
  ⟨R, r + c * sk⟩

/-- Verify a signature: check `[S]·G = R + [c]·vk` where `c = H(R, vk, msg)`. -/
def verify (vk : Pallas.toAffine.Point) (msg : List UInt8)
    (sig : Signature) : Prop :=
  sig.S ⬝ G = sig.R + (challengeHash sig.R vk msg) ⬝ vk

/-- Re-randomize a public key: `rk = vk + [α]·G`. -/
def rerandomizeKey (α : Pasta.Fq) (vk : Pallas.toAffine.Point) :
    Pallas.toAffine.Point :=
  vk + α ⬝ G

/-- Re-randomize a secret key: `rsk = sk + α`. -/
def rerandomizeSk (α : Pasta.Fq) (sk : Pasta.Fq) : Pasta.Fq :=
  sk + α

/-- Negate the scalar component of a signature: `negateS(R, S) = (R, -S)`. -/
def negateS (sig : Signature) : Signature :=
  ⟨sig.R, -sig.S⟩

/-! ## Binding signature (BindingSig)

Orchard also uses RedPallas for `BindingSig`, which proves balance of value
commitments. The algorithm is identical to `SpendAuthSig` but uses a
different generator `BindingG`. -/

/-- The generator point for BindingSig (value commitment randomness base).

Distinct from `G` (the SpendAuthSig generator). -/
axiom BindingG : Pallas.toAffine.Point

/-- The binding generator is not the identity point. -/
axiom BindingG_ne_zero : BindingG ≠ 0

end

end RedPallas
