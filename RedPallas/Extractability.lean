import RedPallas.Spec

namespace RedPallas

/-! # RedDSA key extractability

The Schnorr forking lemma: given two valid signature transcripts with the same
commitment `R` but different challenges `c₁ ≠ c₂`, one can extract the discrete
log of the verification key.

From the two verification equations:
  `[S₁]·gen = R + [c₁]·vk`
  `[S₂]·gen = R + [c₂]·vk`
subtracting yields `[S₁ - S₂]·gen = [c₁ - c₂]·vk`, and dividing by the
nonzero `c₁ - c₂` gives `vk = [(S₁ - S₂)·(c₁ - c₂)⁻¹]·gen`.

This is the algebraic core of knowledge-soundness for Schnorr/RedDSA signatures.
In the random oracle model, the forking lemma (Pointcheval–Stern) produces these
two transcripts from any successful forger; the result here makes that extraction
concrete.

The binding-signature specialization (`binding_extractability`) matches the shape
of Ironwood's `hExtract` hypothesis: from a two-fork on a binding signature, we
extract `bsk` such that `bvk = [bsk]·BindingG`.
-/

open Pasta

noncomputable section

/-- **Schnorr two-fork extraction** (generic over the generator).

Given two valid Schnorr verification equations sharing the same commitment `R`
but with distinct challenges `c₁ ≠ c₂`, the verification key is
`vk = [(S₁ - S₂)·(c₁ - c₂)⁻¹]·gen`. -/
theorem two_fork_extract (gen vk R_sig : Pallas.toAffine.Point)
    (S₁ S₂ c₁ c₂ : Pasta.Fq)
    (hc : c₁ - c₂ ≠ 0)
    (h₁ : S₁ ⬝ gen = R_sig + c₁ ⬝ vk)
    (h₂ : S₂ ⬝ gen = R_sig + c₂ ⬝ vk) :
    vk = ((S₁ - S₂) * (c₁ - c₂)⁻¹) ⬝ gen := by
  have hsub : (S₁ - S₂) ⬝ gen = (c₁ - c₂) ⬝ vk := by
    have h : S₁ ⬝ gen - S₂ ⬝ gen = c₁ ⬝ vk - c₂ ⬝ vk := by
      rw [h₁, h₂, add_sub_add_left_eq_sub]
    rwa [← fqSmul_sub, ← fqSmul_sub] at h
  have key : (c₁ - c₂)⁻¹ ⬝ ((S₁ - S₂) ⬝ gen) = vk := by
    rw [hsub, ← fqSmul_mul, inv_mul_cancel₀ hc, fqSmul_one]
  rw [← key, ← fqSmul_mul, mul_comm]

/-- The extracted secret key from a two-fork. -/
def extractedKey (S₁ S₂ c₁ c₂ : Pasta.Fq) : Pasta.Fq :=
  (S₁ - S₂) * (c₁ - c₂)⁻¹

/-- **SpendAuthSig extractability**: two-fork extraction for the SpendAuthSig generator `G`. -/
theorem spendauth_extractability (vk R_sig : Pallas.toAffine.Point)
    (S₁ S₂ c₁ c₂ : Pasta.Fq)
    (hc : c₁ - c₂ ≠ 0)
    (h₁ : S₁ ⬝ G = R_sig + c₁ ⬝ vk)
    (h₂ : S₂ ⬝ G = R_sig + c₂ ⬝ vk) :
    vk = extractedKey S₁ S₂ c₁ c₂ ⬝ G :=
  two_fork_extract G vk R_sig S₁ S₂ c₁ c₂ hc h₁ h₂

/-- **BindingSig extractability**: two-fork extraction for the BindingSig generator `BindingG`.

This is the algebraic content behind Ironwood's `hExtract` hypothesis: from a
forking-lemma replay of the binding signature, we extract `bsk` such that
`bvk = [bsk]·BindingG`. -/
theorem binding_extractability (bvk R_sig : Pallas.toAffine.Point)
    (S₁ S₂ c₁ c₂ : Pasta.Fq)
    (hc : c₁ - c₂ ≠ 0)
    (h₁ : S₁ ⬝ BindingG = R_sig + c₁ ⬝ bvk)
    (h₂ : S₂ ⬝ BindingG = R_sig + c₂ ⬝ bvk) :
    bvk = extractedKey S₁ S₂ c₁ c₂ ⬝ BindingG :=
  two_fork_extract BindingG bvk R_sig S₁ S₂ c₁ c₂ hc h₁ h₂

/-- Existential form of binding extractability: there exists a scalar `bsk`
such that `bvk = [bsk]·BindingG`. This is the exact shape of Ironwood's
`hExtract` hypothesis. -/
theorem binding_extractability_exists (bvk R_sig : Pallas.toAffine.Point)
    (S₁ S₂ c₁ c₂ : Pasta.Fq)
    (hc : c₁ - c₂ ≠ 0)
    (h₁ : S₁ ⬝ BindingG = R_sig + c₁ ⬝ bvk)
    (h₂ : S₂ ⬝ BindingG = R_sig + c₂ ⬝ bvk) :
    ∃ bsk : Pasta.Fq, bvk = bsk ⬝ BindingG :=
  ⟨extractedKey S₁ S₂ c₁ c₂, binding_extractability bvk R_sig S₁ S₂ c₁ c₂ hc h₁ h₂⟩

end

end RedPallas
