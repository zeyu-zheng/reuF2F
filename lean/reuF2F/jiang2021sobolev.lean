import Mathlib

/-!
# Sobolev Orthogonal Polynomials on the Sierpinski Gasket

Authors: Qingxuan Jiang, Tian Lan, Kasso A. Okoudjou, Robert S. Strichartz,
Shashank Sule, Sreeram Venkat, and Xiaoduo Wang.
Origin: [Cornell SPUR
2019](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: Q. Jiang, T. Lan, K. A. Okoudjou, R. S. Strichartz, S. Sule, S. Venkat, and X. Wang,
*Sobolev orthogonal polynomials on the Sierpinski gasket*, J. Fourier Anal. Appl. **27** (2021),
article 38; arXiv:2010.00107v2.
-/

noncomputable section
namespace Jiang2021Sobolev

/-- The boundary values `alpha_j = P_(j,1)(q1)` (Lemma 2.1). -/
def alpha : ℕ → ℚ
  | 0 => 1
  | 1 => 1 / 6
  | n + 2 =>
      4 / ((5 : ℚ) ^ (n + 2) - 5) *
        ∑ l : Fin (n + 1), alpha (n + 2 - (l.val + 1)) * alpha (l.val + 1)
termination_by n => n
decreasing_by all_goals omega

/-- The boundary values `beta_j = P_(j,2)(q1)` (Lemma 2.1). -/
def beta : ℕ → ℚ
  | 0 => -1 / 2
  | n + 1 =>
      2 / (15 * ((5 : ℚ) ^ (n + 1) - 1)) *
        ∑ l : Fin (n + 1),
          (3 * (5 : ℚ) ^ (n + 1 - l.val) - 5 ^ (l.val + 1) + 6) *
            alpha (n + 1 - l.val) * beta l.val
termination_by n => n
decreasing_by all_goals omega

/-- The boundary normal derivatives `eta_j = ∂_n P_(j,1)(q1)` (Lemma 2.1).
The source's summand `n_l` denotes this same sequence. -/
def eta : ℕ → ℚ
  | 0 => 0
  | n + 1 =>
      (((5 : ℚ) ^ (n + 1) + 1) / 2) * alpha (n + 1) +
        2 * ∑ l : Fin (n + 1), eta l.val * beta (n + 1 - l.val)
termination_by n => n
decreasing_by all_goals omega

/-- The exact family-1 monomial Gram matrix of Section 3.6 (Okoudjou--Strichartz--Tuley,
Lemma 2.1 (16)). -/
def gramEntry (i j : ℕ) : ℚ :=
  2 * ∑ s ∈ Finset.range (min i j + 1),
    (alpha s * eta (i + j + 1 - s) - alpha (i + j + 1 - s) * eta s)

/-- The source `L2` pairing in finitely supported rational monomial coordinates. -/
def gramPairing (a b : ℕ →₀ ℚ) : ℚ :=
  a.sum (fun i x ↦ b.sum (fun j y ↦ x * y * gramEntry i j))

/-- The canonical monic family-1 Legendre coefficients in exact rational coordinates, by the
ordered Gram--Schmidt formula (Remark 3.1). -/
def monicCoefficients (t : ℕ) : ℕ →₀ ℚ :=
  let e := Finsupp.single t (1 : ℚ)
  e - ∑ r : Fin t,
    (gramPairing e (monicCoefficients r.val) /
        gramPairing (monicCoefficients r.val) (monicCoefficients r.val)) •
      monicCoefficients r.val
termination_by t
decreasing_by all_goals omega

/-- **Conjecture 3.1** (arXiv v2, p. 23). The Dirichlet Green image of each canonical monic
family-1 Legendre polynomial has nonzero normal derivative at `q0`.

By Lemma 3.2 and the boundary jets this is stated as the nonvanishing of an exact rational
coefficient sum, omitting the fixed nonzero factor 2. -/
theorem normal_derivative_nonvanishing (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), monicCoefficients t j * alpha (j + 1) ≠ 0 := by
  sorry

end Jiang2021Sobolev
