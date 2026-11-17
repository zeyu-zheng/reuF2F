import Mathlib

/-!
# A melange of diameter Helly-type theorems

Authors: Travis Dillon and Pablo Soberon.
Origin: [NYC Discrete Math REU 2020](https://arxiv.org/pdf/2008.13737v2#page=1).
Reference: T. Dillon and P. Soberon, *A melange of diameter Helly-type theorems*, SIAM J. Discrete
Math. **35** (2021), no. 3, 1615--1627; arXiv:2008.13737v2.
-/

namespace Dillon2021Melange

/-- **Conjecture 1.4**. If every colorful intersection of `2 * d` finite families of convex sets
has diameter at least one, one whole color class has diameter at least `c / √d`, with a positive
constant uniform in the dimension.

Extended diameter retains unbounded sets and does not require endpoint attainment. -/
theorem conjecture_1_4 :
    ∃ c > (0 : ℝ),
      ∀ d > 0, ∀ F : Fin (2 * d) → Finset (Set (EuclideanSpace ℝ (Fin d))),
        (∀ i, ∀ K ∈ F i, Convex ℝ K) →
        (∀ f : Fin (2 * d) → Set (EuclideanSpace ℝ (Fin d)),
          (∀ i, f i ∈ F i) → 1 ≤ Metric.ediam (⋂ i, f i)) →
        ∃ i : Fin (2 * d),
          ENNReal.ofReal (c / √d) ≤
            Metric.ediam (⋂ K ∈ F i, K) := by
  sorry

end Dillon2021Melange
