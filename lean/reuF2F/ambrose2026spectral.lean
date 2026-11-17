import Mathlib

/-!
# Spectral properties of the Schreier graphs of the basilica group

Authors: Kyle Ambrose, Noah Dunham, Michael Morris, Luke G. Rogers, and Alexander Teplyaev.
Origin: [University of Connecticut REU
2025](https://mathreu.uconn.edu/2025/06/09/reu-math-uconn-2025/).
Reference: K. Ambrose, N. Dunham, M. Morris, L. G. Rogers, and A. Teplyaev, *Spectral properties
of the Schreier graphs of the basilica group*, preprint (2026); arXiv:2606.07430v1.
-/

noncomputable section

namespace Ambrose2026Spectral

open MeasureTheory
open scoped ENNReal

/-- The rational functions `ζ_n` with the source's initial data ((4.7)-(4.8)). -/
def zeta : ℕ → RatFunc ℝ
  | 0 => 1
  | 1 => RatFunc.X - 2
  | 2 => (RatFunc.X ^ 2 - 6 * RatFunc.X + 4) / (RatFunc.X - 2)
  | 3 => (RatFunc.X ^ 4 - 12 * RatFunc.X ^ 3 + 42 * RatFunc.X ^ 2 -
      44 * RatFunc.X + 8) / (RatFunc.X ^ 2 - 6 * RatFunc.X + 4)
  | n + 4 => 2 + (1 + 2 / zeta (n + 3)) * (zeta (n + 2) ^ 2 - 4)

/-- **Conjecture 5.13**. Every gap label of the Basilica KNS measure is dyadic.

The measure is the explicit atomic measure of Theorem 5.7, on the distinct real roots of the
reduced numerators of Theorem 4.11. A gap label is the mass to the left of a point outside the
support, so the exterior components give the labels `0` and `1`. -/
theorem conjecture_5_13 :
    let μ : Measure ℝ := Measure.sum fun n : ℕ ↦
      ((6 : ℝ≥0∞) * 2 ^ (n + 1))⁻¹ •
        ∑ x ∈ (zeta (n + 1)).num.roots.toFinset, Measure.dirac x
    ∀ x : ℝ, x ∉ μ.support →
      ∃ j k : ℕ, μ (Set.Iic x) = (j : ℝ≥0∞) / 2 ^ k := by
  sorry

end Ambrose2026Spectral
