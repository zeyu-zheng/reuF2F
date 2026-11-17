import Mathlib

/-!
# Geometric Progression-Free Sequences with Small Gaps

Author: Xiaoyu He.
Origin: [University of Minnesota Duluth REU 2014](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: X. He, *Geometric progression-free sequences with small gaps*, J. Number Theory **151**
(2015), 197–210; doi:10.1016/j.jnt.2014.12.018; arXiv:1501.04121v1.
-/

noncomputable section

namespace He2015Geometric

open MeasureTheory ProbabilityTheory

/-- The family `G_6` of increasing six-term geometric progressions of positive integers with
rational common ratio greater than one. Indexing by tuples counts each progression once. -/
def SixProgression :=
  {g : Fin 6 → ℕ // (∀ i, 0 < g i) ∧
    ∃ r : ℚ, 1 < r ∧ ∀ i : Fin 5,
      (g i.succ : ℚ) = r * (g i.castSucc : ℚ)}

/-- The remaining set `T`, with one of the two middle terms removed from each progression
(Definition 6). -/
def survivingSet (bits : SixProgression → Bool) : Set ℕ :=
  {n | 0 < n ∧ ∀ g : SixProgression,
    n ≠ (if bits g then g.val 2 else g.val 3)}

/-- **Conjecture 10**. For some fixed positive exponent, the random 6-GP-free process has
polylogarithmic gaps with positive probability.

The gap bound is expressed in eventual-interval form, without enumerating the surviving set. -/
theorem conjecture_10 :
    ∃ C > (0 : ℝ),
      0 < Measure.infinitePi (fun _ : SixProgression ↦
          bernoulliMeasure true false ⟨(1 : ℝ) / 2, by norm_num⟩)
        {bits : SixProgression → Bool |
        ∃ K > (0 : ℕ), ∃ N ≥ (2 : ℕ),
          ∀ x ≥ N, ∃ n : ℕ,
            n ∈ survivingSet bits ∧ x < n ∧
              (n : ℝ) ≤ x + K * (Real.log (x : ℝ)) ^ C} := by
  sorry

end He2015Geometric
