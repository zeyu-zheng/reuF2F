import Mathlib

/-!
# Pattern Problems related to the Arithmetic Kakeya Conjecture

Authors: Charlie Cowen-Breen, Elene Karangozishvili, Narmada Varadarajan, and Thomas Wang.
Origin: [Budapest Semesters in Mathematics](https://www.bsmath.hu/articles.html).
Reference: C. Cowen-Breen, E. Karangozishvili, N. Varadarajan, and T. Wang, *Pattern problems
related to the arithmetic Kakeya conjecture*, preprint (2020), arXiv:2011.07056v1, 30 pp.
-/

namespace CowenBreen2020Pattern

open Topology
open Finset

/-- The least cardinality `G'_U(N)` of an integer set containing an affine copy of `U` with each
of `N` distinct integer basepoints and nonzero scaling (Section 2.1). -/
noncomputable def patternCardinality (U : Finset ℚ) (N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ B : Finset ℤ, ∃ S : Finset ℤ,
    #B = m ∧ #S = N ∧
      ∀ x ∈ S, ∃ r ≠ (0 : ℚ),
        ∀ u ∈ U, ∃ b : ℤ,
          b ∈ B ∧ (b : ℚ) = (x : ℚ) + r * u}

/-- **Conjecture 2.1**. For every increasing chain of positive rational patterns of cardinality
`k`, the limiting logarithmic growth exponents of `G'` tend to one. -/
theorem conjecture_2_1 (U : ℕ → Finset ℚ) (hU : Monotone U)
    (hcard : ∀ k : ℕ, #(U k) = k)
    (hpos : ∀ k : ℕ, ∀ u ∈ U k, 0 < u) :
    ∃ L : ℕ → ℝ,
      (∀ k > 0,
        Filter.Tendsto
          (fun N : ℕ ↦ Real.log (patternCardinality (U k) N : ℝ) / Real.log (N : ℝ))
          Filter.atTop (𝓝 (L k))) ∧
      Filter.Tendsto L Filter.atTop (𝓝 1) := by
  sorry

end CowenBreen2020Pattern
