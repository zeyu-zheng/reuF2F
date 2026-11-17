import Mathlib

/-!
# A monotonicity conjecture for the local maximal singularity of the Hilbert scheme of points

Authors: Alexia Ascott, Fatemeh Rezaee, and Zhichen Zhou.
Origin: [Cambridge SRIM 2024](https://arxiv.org/abs/2506.17704v2).
Reference: A. Ascott, F. Rezaee, and Z. Zhou, *A monotonicity conjecture for the local maximal
singularity of the Hilbert scheme of points*, preprint, 8 pp.; arXiv:2506.17704v2 (2026; first
version 2025).
-/

noncomputable section

namespace Ascott2025Monotonicity

/-- The complex polynomial ring in `N` ordered variables. -/
abbrev PolynomialRing (N : ℕ) := MvPolynomial (Fin N) ℂ

/-- Borel-fixed monomial ideals, i.e. strongly stable monomial ideals in characteristic zero. -/
def IsBorelFixed {N : ℕ} (I : Ideal (PolynomialRing N)) : Prop :=
  (∃ S : Set (Fin N →₀ ℕ),
    I = Ideal.span ((fun d ↦ MvPolynomial.monomial d (1 : ℂ)) '' S)) ∧
  ∀ d : Fin N →₀ ℕ, MvPolynomial.monomial d (1 : ℂ) ∈ I →
    ∀ i j : Fin N, i < j → 0 < d j →
      MvPolynomial.monomial
        (d - Finsupp.single j 1 + Finsupp.single i 1) (1 : ℂ) ∈ I

/-- The least exponent `m_i` with `x_i ^ m_i ∈ I`. -/
def pureExponent {N : ℕ} (I : Ideal (PolynomialRing N)) (i : Fin N) : ℕ :=
  sInf {m : ℕ | MvPolynomial.X i ^ m ∈ I}

/-- The tangent dimension `T(I)`: the complex dimension of `Hom_R(I, R / I)`. -/
def tangentDimension {N : ℕ} (I : Ideal (PolynomialRing N)) : ℕ :=
  Module.finrank ℂ (I →ₗ[PolynomialRing N] (PolynomialRing N ⧸ I))

/-- **Conjecture C** (p. 2). For fixed colength, the maximal tangent dimension of Borel-fixed
ideals strictly increases with the smallest pure exponent.

"Increasing" is read as strict, following the stated consequence and Figure 1. The
for-all-`I`/exists-`J` form is equivalent since fiber maxima are attained, and the binomial bound
makes the higher-exponent fiber nonempty. -/
theorem conjecture_c {N : ℕ} (l m n : ℕ) (hN : 3 ≤ N) (hl : 0 < l)
    (hm : 0 < m) (hmn : m < n) (hn : Nat.choose (N + n - 1) N ≤ l)
    (I : Ideal (PolynomialRing N)) (hI : IsBorelFixed I)
    (hlength : Module.finrank ℂ (PolynomialRing N ⧸ I) = l)
    (hexponent : pureExponent I ⟨0, by omega⟩ = m) :
    ∃ J : Ideal (PolynomialRing N), IsBorelFixed J ∧
      Module.finrank ℂ (PolynomialRing N ⧸ J) = l ∧
      pureExponent J ⟨0, by omega⟩ = n ∧ tangentDimension I < tangentDimension J := by
  sorry

end Ascott2025Monotonicity
