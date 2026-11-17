import Mathlib

/-!
# Optimal Bounds for the Number of Pieces of Real Near-Circuit Hypersurfaces

Authors: Weixun Deng, J. Maurice Rojas, and Cordelia Russell.
Origin: [Texas A&M University REU
2024](https://artsci.tamu.edu/mathematics/academics/undergraduate/research/reu/results/results-2024.html).
Reference: W. Deng, J. M. Rojas, and C. Russell, *Optimal bounds for the number of pieces of real
near-circuit hypersurfaces*, ISSAC 2025 (2025), 9 pp.; doi:10.1145/3747199.3747576.
-/

namespace Deng2025Optimal

open Finset

/-- No `n + 1` distinct support points lie in an affine hyperplane (p. 1). -/
def GenericSupport {n : ℕ} (A : Finset (Fin n → ℝ)) : Prop :=
  ∀ S : Finset (Fin n → ℝ), S ⊆ A → #S = n + 1 →
    AffineIndependent ℝ (fun a : S ↦ a.val)

/-- The positive zero set (p. 1). Exponents are arbitrary reals, as the p. 1 footnote permits. -/
def positiveZeroSet {n : ℕ} (f : (Fin n → ℝ) →₀ ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧
    f.sum (fun a c ↦ c * ∏ i : Fin n, x i ^ a i) = 0}

/-- **Unnumbered conjecture** (after Example 1.6, p. 2). In every dimension `n ≥ 4` a generic,
honest real-exponent near-circuit has exactly three positive connected components.

Unlike the separate upper-bound theorem, no smoothness or coefficient sign pattern is imposed. -/
theorem three_components_in_every_dimension (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : (Fin n → ℝ) →₀ ℝ,
      #f.support = n + 3 ∧
      affineSpan ℝ (f.support : Set (Fin n → ℝ)) = ⊤ ∧
      GenericSupport f.support ∧
      Nonempty (ConnectedComponents (positiveZeroSet f) ≃ Fin 3) := by
  sorry

end Deng2025Optimal
