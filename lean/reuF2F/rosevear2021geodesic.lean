import Mathlib

/-!
# Geodesic motion on SL(n) with the Hilbert-Schmidt metric

Authors: Audrey Rosevear, Samuel Sottile, and Willie W. Y. Wong.
Origin: [Michigan State University SURIEM
2020](https://www.nsf.gov/awardsearch/showAward?AWD_ID=1852066).
Reference: A. Rosevear, S. Sottile, and W. W. Y. Wong, *Geodesic motion on SL(n) with the
Hilbert-Schmidt metric*, La Matematica **1** (2022), 343-386; arXiv:2101.09266v2.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius

namespace Rosevear2021Geodesic

/-- **Conjecture 6.1** (p. 42). In odd dimension, every nonconstant complete Hilbert-Schmidt
geodesic on SL(n) is unbounded.

Equation (8) gives the geodesic condition; nonzero velocity excludes the static solutions of
p. 38, a convention read from context. -/
theorem conjecture_6_1 {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (hA : ContDiff ℝ 2 A)
    (hSL : ∀ t : ℝ, (A t).det = 1)
    (hgeodesic : ∀ t : ℝ,
      deriv (deriv A) t =
        ((deriv A t * (A t)⁻¹ * deriv A t * (A t)⁻¹).trace /
          ((A t)⁻¹ * ((A t)⁻¹)ᵀ).trace) • ((A t)⁻¹)ᵀ)
    (hregular : deriv A 0 ≠ 0) :
    ¬Bornology.IsBounded (Set.range A) := by
  sorry

end Rosevear2021Geodesic
