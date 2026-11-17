import Mathlib

/-!
# Machine learning optimization algorithms related to gradient descent

Author: Minh Le.
Origin: [University of Massachusetts Amherst REU
2023](https://sites.google.com/umass.edu/math-stat-reu/reports-2023).
Reference: M. Le, *Machine learning optimization algorithms related to gradient descent*, UMass
Amherst REU report, August 18, 2023.
-/

noncomputable section

namespace Le2023Machine

/-- **Open question** (Section 3, Future Work, p. 17; cf. p. 16). The Nesterov ODE has
inverse-quadratic objective-gap decay under the global Polyak-Lojasiewicz condition and a
globally Lipschitz gradient, without convexity.

The continuous-time reading follows equation (11) and its stated initial data; it is not a
discrete-rate transfer, a sharp exponent, or a uniform convex-case prefactor. Luo-Xiao's
related theorems (2023 Theorem 2.3, Proposition 3.2) assume extra global growth and radial
flatness. -/
theorem nesterov_ode_pl_rate
    (d : ℕ) (hd : 0 < d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hf : ContDiff ℝ 1 f)
    (xstar x₀ : EuclideanSpace ℝ (Fin d))
    (hmin : ∀ z, f xstar ≤ f z)
    (hgrad : LipschitzWith (Real.toNNReal L) (gradient f))
    (hPL : ∀ z, f z - f xstar ≤ ‖gradient f z‖ ^ 2 / (2 * μ))
    (X : ℝ → EuclideanSpace ℝ (Fin d))
    (hC1 : ContDiffOn ℝ 1 X (Set.Ici (0 : ℝ)))
    (hC2 : ContDiffOn ℝ 2 X (Set.Ioi (0 : ℝ)))
    (hinit : X 0 = x₀)
    (hvelocity : HasDerivWithinAt X 0 (Set.Ici (0 : ℝ)) 0)
    (hODE : ∀ t > 0,
      deriv (deriv X) t + ((3 : ℝ) / t) • deriv X t +
        gradient f (X t) = 0) :
    ∃ C > 0, ∃ T > 0, ∀ t ≥ T, f (X t) - f xstar ≤ C / t ^ 2 := by
  sorry

end Le2023Machine
