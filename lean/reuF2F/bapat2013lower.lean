import Mathlib

/-!
# Lower central series of free algebras in symmetric tensor categories

Authors: Asilata Bapat and David Jordan.
Origin: [MIT SPUR 2009](https://asilatabapat.org/assets/papers/2009-bapat-lcq.pdf).
Reference: A. Bapat and D. Jordan, *Lower central series of free algebras in symmetric tensor
categories*, J. Algebra **373** (2013), 299-311; arXiv:1001.1375v3.
-/

noncomputable section

namespace Bapat2013Lower

/-- The free superalgebra, with the first `m` generators even and the last `n` odd (Section 5). -/
abbrev A (m n : ℕ) := MonoidAlgebra ℂ (FreeMonoid (Fin (m + n)))

/-- The supercommutator, extended bilinearly from homogeneous words (Section 5). -/
def superBracket {m n : ℕ} (a b : A m n) : A m n :=
  a.coeff.sum fun w c ↦ b.coeff.sum fun v d ↦
    MonoidAlgebra.single (w * v) (c * d) -
      MonoidAlgebra.single (v * w)
        ((-1 : ℂ) ^
          (w.toList.countP (fun i ↦ m ≤ i.val) *
            v.toList.countP (fun i ↦ m ≤ i.val)) * c * d)

/-- The lower central series (Sections 1 and 3). Index `r` denotes `L_(r+1)`. -/
def lowerCentral (m n : ℕ) : ℕ → Submodule ℂ (A m n)
  | 0 => ⊤
  | r + 1 => Submodule.span ℂ
      {z | ∃ a b, b ∈ lowerCentral m n r ∧ z = superBracket a b}

/-- The multidegree-`e` component, spanned by all words with the prescribed multiplicities. -/
def homogeneousPiece {m n : ℕ} (e : Fin (m + n) →₀ ℕ) :
    Submodule ℂ (A m n) :=
  Submodule.span ℂ
    {z | ∃ w : FreeMonoid (Fin (m + n)),
      (∀ i, w.toList.count i = e i) ∧ z = MonoidAlgebra.single w 1}

/-- The multigraded Hilbert series of `L_k / L_(k+1)` (Section 5). -/
def hilbertSeries (m n k : ℕ) : MvPowerSeries (Fin (m + n)) ℤ := fun e ↦
  let U := lowerCentral m n (k - 1) ⊓ homogeneousPiece e
  (Module.finrank ℂ (U ⧸ (lowerCentral m n k).comap U.subtype) : ℤ)

/-- **Conjecture 8.1** (Section 8). Every lower central quotient in the stated range has a
multigraded Hilbert series with the prescribed simple denominator.

The polynomial numerator may cancel factors; the denominator need not be reduced. -/
theorem conjecture_8_1 (m n k : ℕ) (hk : 3 ≤ k) :
    ∃ P : MvPolynomial (Fin (m + n)) ℤ,
      hilbertSeries m n k *
        (∏ i : Fin (m + n), (1 - MvPowerSeries.X i)) =
          (P : MvPowerSeries (Fin (m + n)) ℤ) := by
  sorry

end Bapat2013Lower
