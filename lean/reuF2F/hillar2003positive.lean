import Mathlib

/-!
# Positive eigenvalues of generalized words in two Hermitian positive definite matrices

Authors: Christopher J. Hillar and Charles R. Johnson.
Origin: [William & Mary REU 1999](https://arxiv.org/abs/math/0504587).
Reference: C. J. Hillar and C. R. Johnson, *Positive eigenvalues of generalized words in two
Hermitian positive definite matrices*, Fields Inst. Commun. **37** (2003), 111–122;
arXiv:math/0504587v1.
-/

noncomputable section

open scoped MatrixOrder ComplexOrder

namespace Hillar2003Positive

/-- Generalized words in two letters with real exponents and the usual power cancellations. -/
abbrev GWord := Monoid.Coprod (Multiplicative ℝ) (Multiplicative ℝ)

/-- The reversal of a word, keeping each exponent and reversing the order of the factors. -/
def reversal (w : GWord) : GWord :=
  (Monoid.Coprod.map invMonoidHom invMonoidHom w)⁻¹

/-- Nearly symmetric words: products of two words fixed by reversal. -/
def NearlySymmetric (w : GWord) : Prop :=
  ∃ u v : GWord, w = u * v ∧ reversal u = u ∧ reversal v = v

/-- Evaluation of a generalized word by primary real powers of the two positive matrices. -/
def eval {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) (hB : B.PosDef) :
    GWord →* Matrix (Fin n) (Fin n) ℂ :=
  let a : Multiplicative ℝ →* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p ↦ CFC.rpow A p.toAdd
      map_one' := CFC.rpow_zero A hA.posSemidef.nonneg
      map_mul' := fun _ _ ↦ CFC.rpow_add hA.isUnit }
  let b : Multiplicative ℝ →* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun p ↦ CFC.rpow B p.toAdd
      map_one' := CFC.rpow_zero B hB.posSemidef.nonneg
      map_mul' := fun _ _ ↦ CFC.rpow_add hB.isUnit }
  Monoid.Coprod.lift a b

/-- A good generalized word, with strictly positive real eigenvalues in every positive dimension. -/
def Good (w : GWord) : Prop :=
  ∀ n > 0, ∀ (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (hB : B.PosDef),
    ∀ z ∈ spectrum ℂ (eval A B hA hB w), z.im = 0 ∧ 0 < z.re

/-- **Conjecture 1.3**. A generalized real-power word is good exactly when it is nearly
symmetric. -/
theorem conjecture_1_3 (w : GWord) : Good w ↔ NearlySymmetric w := by
  sorry

end Hillar2003Positive
