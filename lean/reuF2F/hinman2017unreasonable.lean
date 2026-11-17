import Mathlib

/-!
# The Unreasonable Rigidity of Ulam Sets

Authors: Joshua Hinman, Borys Kuca, Alexander Schlesinger, and Arseniy Sheydvasser.
Origin: [Yale SUMRY 2017](https://sumry.yale.edu/past-projects).
Reference: J. Hinman, B. Kuca, A. Schlesinger, and A. Sheydvasser, *The Unreasonable Rigidity of
Ulam Sets*, arXiv:1711.00145v1 (2017).
-/

namespace Hinman2017Unreasonable

/-- Membership in the generalized Ulam sequence seeded by `1` and `b`: after the seeds, a number
belongs when it has exactly one ordered increasing pair of smaller Ulam summands. -/
def IsUlam (b k : ℕ) : Prop :=
  if k ≤ b then k = 1 ∨ k = b else
    ∃! p : Fin k × Fin k,
      p.1.val < p.2.val ∧ p.1.val + p.2.val = k ∧
        IsUlam b p.1.val ∧ IsUlam b p.2.val
termination_by k

/-- **Conjecture 1.1**. For every `n ≥ 4`, the interval endpoints of the complete `U(1,n)` follow
one common integer-affine family.

Intervals are the ordered nonempty maximal runs of Section 3 (cf. Sheydvasser, arXiv:1910.00109v2,
Conjecture 1.3), separated by `upper_i + 1 < lower_(i+1)`, since the printed inequalities do not
express maximality. -/
theorem rigidity :
    ∃ m p k r : ℕ → ℤ, ∀ n ≥ (4 : ℕ),
      (∀ i : ℕ, m i * (n : ℤ) + p i ≤ k i * (n : ℤ) + r i ∧
        k i * (n : ℤ) + r i + 1 < m (i + 1) * (n : ℤ) + p (i + 1)) ∧
        Int.ofNat '' {t : ℕ | IsUlam n t} =
          ⋃ i : ℕ, Set.Icc (m i * (n : ℤ) + p i) (k i * (n : ℤ) + r i) := by
  sorry

end Hinman2017Unreasonable
