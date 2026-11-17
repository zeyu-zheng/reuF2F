import Mathlib

/-!
# Convexity properties of sections of 1-symmetric bodies and Rademacher sums

Authors: Joseph Kalarickal, David Rotunno, Salil Singh, and Tomasz Tkocz.
Origin: [Carnegie Mellon University SURF
2022](https://www.cmu.edu/math/undergrad/surf-sems-2022.html).
Reference: J. Kalarickal, D. Rotunno, S. Singh, and T. Tkocz, *Convexity properties of sections
of 1-symmetric bodies and Rademacher sums*, Proc. Amer. Math. Soc. Ser. B **12** (2025),
187-196; arXiv:2312.13922v3.
-/

namespace Kalarickal2023Convexity

open MeasureTheory

/-- **Unnumbered conjecture** (Section 3.2, final paragraph; arXiv v3, p. 9). The negative
logarithm of negative moments of exponentially weighted sums of independent uniform vectors on
the Euclidean two-sphere is convex, for every exponent between zero and one. -/
theorem negative_moment_log_convexity (n : ℕ) (hn : 0 < n)
    (q : ℝ) (hq : 0 < q) (hq_one : q ≤ 1) :
    ConvexOn ℝ Set.univ (fun t : Fin n → ℝ ↦
      -Real.log (∫ x, ‖∑ i, Real.exp (t i) • (x i).val‖ ^ (-q)
        ∂(Measure.pi (fun _ : Fin n ↦ ProbabilityTheory.cond
          (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)))) := by
  sorry

end Kalarickal2023Convexity
