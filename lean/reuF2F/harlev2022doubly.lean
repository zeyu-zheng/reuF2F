import Mathlib

/-!
# The Doubly Stochastic Single Eigenvalue Problem: A Computational Approach

Authors: Amit Harlev, Charles R. Johnson, and Derek Lim.
Origin: [William & Mary REU](https://arxiv.org/pdf/1911.07353v2).
Reference: A. Harlev, C. R. Johnson, and D. Lim, *The doubly stochastic single eigenvalue problem:
a computational approach*, Experimental Mathematics **31** (2022), no. 3, 936–945;
arXiv:1908.03647v2.
-/

namespace Harlev2022Doubly

/-- **Conjecture 2.7** (Boundary Conjecture). Every boundary point of the union of doubly
stochastic spectra is attained by a convex combination of at most two permutation matrices. -/
theorem conjecture_2_7 (n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : z ∈ frontier {w : ℂ | ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A ∈ doublyStochastic ℝ (Fin n) ∧
        w ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ))}) :
    ∃ σ τ : Equiv.Perm (Fin n), ∃ t ∈ Set.Icc (0 : ℝ) 1,
      z ∈ spectrum ℂ (t • σ.permMatrix ℂ + (1 - t) • τ.permMatrix ℂ) := by
  sorry

end Harlev2022Doubly
