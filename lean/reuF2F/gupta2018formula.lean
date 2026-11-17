import Mathlib

/-!
# A formula for F-Polynomials in terms of C-Vectors and Stabilization of F-Polynomials

Author: Meghal Gupta.
Origin: [University of Minnesota Twin Cities REU
2018](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: M. Gupta, *A formula for F-Polynomials in terms of C-Vectors and Stabilization of
F-Polynomials*, arXiv:1812.01910 (2018), revised 2019.
-/

noncomputable section

namespace Gupta2018Formula

/-- Ordinary quiver mutation. Mutable rows are on the left and frozen rows on the right of the
index sum, and positive entries count row-to-column arrows. -/
def mutateQuiver {r : ℕ} (Q : Matrix (Fin r ⊕ Fin r) (Fin r) ℤ)
    (k : Fin r) : Matrix (Fin r ⊕ Fin r) (Fin r) ℤ :=
  fun i j ↦ if i = Sum.inl k ∨ j = k then -Q i j else
    Q i j + max (Q i k) 0 * max (Q (Sum.inl k) j) 0 -
      max (-Q i k) 0 * max (-Q (Sum.inl k) j) 0

/-- The exchange-label part of ordinary quiver mutation. -/
def mutateLabels {r : ℕ} (Q : Matrix (Fin r ⊕ Fin r) (Fin r) ℤ)
    (V : Fin r ⊕ Fin r → FractionRing (MvPolynomial (Fin r) ℚ)) (k : Fin r) :
    Fin r ⊕ Fin r → FractionRing (MvPolynomial (Fin r) ℚ) :=
  fun i ↦ if i = Sum.inl k then
    ((∏ j, V j ^ (Q j k).toNat) + (∏ j, V j ^ (-Q j k).toNat)) /
      V (Sum.inl k)
    else V i

/-- The signed frozen-row, mutable-column block after the given mutations (Definition 2.21). It
starts from the principal framing `i' → i`. -/
def cMatrix {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ) (w : List (Fin r)) :
    Matrix (Fin r) (Fin r) ℤ :=
  let Q := w.foldl mutateQuiver (Matrix.fromRows B 1)
  fun i j ↦ Q (Sum.inr i) j

/-- The deformed polynomial obtained by applying `-C⁻¹` to the exponents of the just-mutated
F-polynomial (Definition 2.26). It is realized by monomial substitution in the initial frozen
labels and replay of the exchange sequence. -/
def sPolynomial {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (w : List (Fin r)) (k : Fin r) : FractionRing (MvPolynomial (Fin r) ℚ) :=
  let M := -(cMatrix B (w ++ [k]))⁻¹
  let V : Fin r ⊕ Fin r → FractionRing (MvPolynomial (Fin r) ℚ) :=
    Sum.elim (fun _ ↦ 1) (fun i ↦
      ∏ j, (algebraMap (MvPolynomial (Fin r) ℚ)
        (FractionRing (MvPolynomial (Fin r) ℚ)) (MvPolynomial.X j)) ^ (M j i))
  let final := (w ++ [k]).foldl
    (fun state v ↦ (mutateQuiver state.1 v, mutateLabels state.1 state.2 v))
    (Matrix.fromRows B 1, V)
  final.2 (Sum.inl k)

/-- **Conjecture 8.2**. Every deformed F-polynomial of an ordinary framed quiver is a polynomial,
for every nonempty mutable mutation sequence.

The ordinary-mutation and signed-C conventions resolve the duplicated path bullet and omitted
reverse-arrow sign in the printed definitions; the full non-green domain is retained. -/
theorem conjecture_8_2 {r : ℕ} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : ∀ i j, B i j = -B j i) (w : List (Fin r)) (k : Fin r) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      algebraMap (MvPolynomial (Fin r) ℚ) (FractionRing (MvPolynomial (Fin r) ℚ)) P =
        sPolynomial B w k := by
  sorry

end Gupta2018Formula
