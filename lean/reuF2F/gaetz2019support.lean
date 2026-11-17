import Mathlib

/-!
# Support Equalities Among Ribbon Schur Functions

Authors: Marisa Gaetz, Will Hardt, and Shruthi Sridhar.
Origin: [University of Minnesota Twin Cities REU
2017](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: M. Gaetz, W. Hardt, and S. Sridhar, *Support equalities among ribbon Schur
functions*, preprint; arXiv:1709.03011v2.
-/

namespace Gaetz2019Support

open Finset

/-- The cells of a ribbon with rows read top to bottom, adjacent rows overlapping in one column
(Section 2.2). Coordinates increase downward and rightward. -/
def ribbonCells {m : ℕ} (a : Fin m → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion fun r : Fin m ↦
    (Finset.range (a r)).image fun c ↦
      (r.val, ∑ s : Fin m with r < s, (a s - 1) + c)

/-- The Schur support, via the Littlewood-Richardson tableaux of Corollary 2.10 (Definition 2.1).
Labels are zero-based, and prefixes are read right to left, then top to bottom. -/
def schurSupport (D : Finset (ℕ × ℕ)) : Set YoungDiagram :=
  {μ | ∃ T : D → ℕ,
    (∀ b c : D, b.val.1 = c.val.1 → b.val.2 < c.val.2 → T b ≤ T c) ∧
    (∀ b c : D, b.val.2 = c.val.2 → b.val.1 < c.val.1 → T b < T c) ∧
    (∀ (b : D) (i : ℕ),
      #{c : D | (c.val.1 < b.val.1 ∨ (c.val.1 = b.val.1 ∧ b.val.2 ≤ c.val.2)) ∧
          T c = i + 1} ≤
      #{c : D | (c.val.1 < b.val.1 ∨ (c.val.1 = b.val.1 ∧ b.val.2 ≤ c.val.2)) ∧
          T c = i}) ∧
    (∀ i : ℕ, #{b : D | T b = i} = μ.rowLen i)}

/-- **Conjecture 4.8** (p. 21). A decreasing ribbon has the same Schur support under every
permutation of its rows exactly when all the stated inequalities for `N_j` hold. -/
theorem conjecture_4_8 {m : ℕ} (hm : 3 ≤ m) (a : Fin m → ℕ)
    (ha : ∀ i, 2 ≤ a i) (horder : Antitone a) :
    (∀ p : Equiv.Perm (Fin m),
      schurSupport (ribbonCells a) = schurSupport (ribbonCells (fun i ↦ a (p i)))) ↔
    (∀ j ≥ 1, j + 2 ≤ m →
      sSup {k : ℕ | ∑ i : Fin m with i.val < j, (k - a i) ≤ m - j - 2} <
        (∑ i : Fin m with j ≤ i.val, a i) - (m - j - 2)) := by
  sorry

end Gaetz2019Support
