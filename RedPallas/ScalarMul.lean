import Pasta.Fields
import Pasta.Pallas

namespace RedPallas

/-! # Scalar multiplication by Fq on Pallas

The Pallas curve group has prime order `Fq.p`. This allows us to define
scalar multiplication by elements of `Fq = ZMod Fq.p` via the natural
number representative, and derive linearity from the group order.

See §5.4.7.1 of the Zcash protocol specification.
-/

open Pasta

noncomputable section

/-- The Pallas curve group has order `Fq.p`.

This is the fundamental axiom connecting the curve group to its scalar
field. In practice this follows from the point-counting result for Pallas,
but we axiomatize it here. -/
axiom order_pallas (P : Pallas.toAffine.Point) : Fq.p • P = 0

/-- Scalar multiplication of a Pallas point by an element of `Fq`.

Defined via the natural number representative: `s ⬝ P = [s.val] · P`. -/
def fqSmul (s : Pasta.Fq) (P : Pallas.toAffine.Point) : Pallas.toAffine.Point :=
  s.val • P

scoped infixl:70 " ⬝ " => fqSmul

@[simp]
theorem fqSmul_def (s : Pasta.Fq) (P : Pallas.toAffine.Point) :
    s ⬝ P = s.val • P := rfl

/-- Reducing `nsmul` modulo the group order does not change the result. -/
theorem nsmul_mod_order (m : ℕ) (P : Pallas.toAffine.Point) :
    (m % Fq.p) • P = m • P := by
  conv_rhs =>
    rw [show m = Fq.p * (m / Fq.p) + m % Fq.p from (Nat.div_add_mod m Fq.p).symm]
  rw [add_nsmul, mul_nsmul, order_pallas, nsmul_zero, zero_add]

/-- Fq-scalar multiplication distributes over scalar addition. -/
theorem fqSmul_add (a b : Pasta.Fq) (P : Pallas.toAffine.Point) :
    (a + b) ⬝ P = a ⬝ P + b ⬝ P := by
  simp only [fqSmul_def, ZMod.val_add]
  rw [nsmul_mod_order, add_nsmul]

/-- Fq-scalar multiplication respects scalar multiplication. -/
theorem fqSmul_mul (a b : Pasta.Fq) (P : Pallas.toAffine.Point) :
    (a * b) ⬝ P = a ⬝ (b ⬝ P) := by
  simp only [fqSmul_def, ZMod.val_mul]
  rw [nsmul_mod_order, mul_nsmul']

/-- Fq-scalar multiplication distributes over point addition. -/
theorem fqSmul_add_right (s : Pasta.Fq) (P Q : Pallas.toAffine.Point) :
    s ⬝ (P + Q) = s ⬝ P + s ⬝ Q := by
  simp only [fqSmul_def]
  exact smul_add s.val P Q

/-- Scalar multiplication by zero gives the identity. -/
@[simp]
theorem fqSmul_zero (P : Pallas.toAffine.Point) :
    (0 : Pasta.Fq) ⬝ P = 0 := by
  simp [fqSmul_def, ZMod.val_zero]

/-- Scalar multiplication by one is the identity. -/
@[simp]
theorem fqSmul_one (P : Pallas.toAffine.Point) :
    (1 : Pasta.Fq) ⬝ P = P := by
  simp [fqSmul_def, ZMod.val_one]

end

end RedPallas
