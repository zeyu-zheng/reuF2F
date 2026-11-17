import Mathlib

/-!
# Subsets of F_q[x] free of 3-term geometric progressions

Authors: Megumi Asada, Eva Fourakis, Sarah Manski, Nathan McNew, Steven J. Miller, and
Gwyneth Moreland.
Origin: [Williams College SMALL REU 2015](https://www.nathanmcnew.com/math.html).
Reference: M. Asada, E. Fourakis, S. Manski, N. McNew, S. J. Miller, and G. Moreland, *Subsets of
F_q[x] free of 3-term geometric progressions*, Finite Fields Appl. **44** (2017), 135-147;
doi:10.1016/j.ffa.2016.10.002; arXiv:1512.01932v2.
-/

noncomputable section

namespace Asada2017Subsets

open Finset

open scoped Classical in
/-- Upper density along degree cutoffs, an equivalent form of the upper density of
Definition 4.1. Each polynomial of degree at most `n` is counted once. -/
def upperDensity (K : Type*) [Field K] [Fintype K] (A : Set (Polynomial K)) : ℝ :=
  Filter.limsup (fun n : ℕ ↦
    let B := Finset.univ.image (Polynomial.ofFn (R := K) (n + 1))
    ((#{f ∈ B | f ∈ A} : ℝ) / (#B : ℝ))) Filter.atTop

/-- **Conjecture 6.3** (arXiv v2, p. 11). Over every finite field, the supremum of upper
densities of sets avoiding three-term progressions with nonunit polynomial ratio equals `m_q`
from Theorem 4.3.

The supremum is over all subsets, not only sets determined by degree. Only nonzero starts and
nonunit polynomial ratios are forbidden; Definition 4.1's `A ⊆ F_q` is read as `A ⊆ F_q[x]`. -/
theorem conjecture_6_3 (K : Type*) [Field K] [Fintype K] :
    sSup {d : ℝ | ∃ A : Set (Polynomial K),
      (∀ f r : Polynomial K, f ≠ 0 → r ≠ 0 → ¬IsUnit r →
        f ∈ A → f * r ∈ A → f * r ^ 2 ∉ A) ∧ upperDensity K A = d} =
      (1 - ((Fintype.card K : ℝ)⁻¹) ^ 2) *
        ∏' i : ℕ, (1 + ((Fintype.card K : ℝ)⁻¹) ^ (3 ^ (i + 1))) := by
  sorry

end Asada2017Subsets
