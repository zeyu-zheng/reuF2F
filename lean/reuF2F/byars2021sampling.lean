import Mathlib

/-!
# Sampling and interpolation of cumulative distribution functions of Cantor sets in [0, 1]

Authors: Allison Byars, Evan Camrud, Steven N. Harding, Sarah McCarty,
Keith Sullivan, and Eric S. Weber.
Origin: [Iowa State University REU 2019](https://www.mathreu.org/publications).
Reference: A. Byars, E. Camrud, S. N. Harding, S. McCarty, K. Sullivan, and E. S. Weber,
*Sampling and interpolation of cumulative distribution functions of Cantor sets in [0, 1]*,
Demonstr. Math. **54** (2021), 85-109; https://par.nsf.gov/servlets/purl/10314055/10314055.pdf.
-/

noncomputable section

namespace Byars2021Sampling

open MeasureTheory ProbabilityTheory
open Finset

/-- **Unnumbered conjecture** (Introduction, p. 2). For each known scale `N ≥ 3`, the minimum
number of fixed nonadaptive samples distinguishing all admissible Cantor CDFs is `⌊N / 2⌋`.

The CDF uses independent uniform allowed digits; empty, singleton and full digit sets are
excluded. -/
theorem minimum_fixed_sampling (N : ℕ) (hN : 3 ≤ N) :
    let F : {D : Finset (Fin N) // 2 ≤ #D ∧ #D < N} → unitInterval → ℝ :=
      fun D x ↦
        cdf ((Measure.infinitePi (fun _ : ℕ ↦
            (PMF.uniformOfFinset D.val (Finset.card_pos.mp (by omega))).toMeasure)).map
          (Real.ofDigits : (ℕ → Fin N) → ℝ)) (x : ℝ)
    (∃ S : Finset unitInterval, #S = N / 2 ∧
      ∀ D E, (∀ x ∈ S, F D x = F E x) → F D = F E) ∧
    (∀ S : Finset unitInterval, #S < N / 2 →
      ∃ D E, F D ≠ F E ∧ ∀ x ∈ S, F D x = F E x) := by
  sorry

end Byars2021Sampling
