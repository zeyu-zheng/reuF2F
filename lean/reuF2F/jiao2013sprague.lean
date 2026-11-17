import Mathlib

/-!
# On the Sprague-Grundy Values of the F-Wythoff Game

Author: Yang Jiao.
Origin: [University of Minnesota Duluth REU 2012](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: Y. Jiao, *On the Sprague-Grundy values of the F-Wythoff game*, Electron. J. Combin.
**20** (2013), no. 1, Paper 14, 12 pp.
-/

noncomputable section

namespace Jiao2013Sprague

open scoped Topology

/-- The Sprague-Grundy value: the least natural number absent from all legal followers
(Section 1). Diagonal moves preserve the integer ratio and leave both piles positive. -/
def grundy (a b : ℕ) : ℕ :=
  sInf {g : ℕ |
    (∀ c : Fin a, grundy c.val b ≠ g) ∧
    (∀ d : Fin b, grundy a d.val ≠ g) ∧
    (∀ t : Fin (min a b), 0 < t.val →
      (max a b - t.val) / (min a b - t.val) = max a b / min a b →
        grundy (a - t.val) (b - t.val) ≠ g)}
termination_by a + b
decreasing_by
  all_goals omega

/-- The smaller coordinate of the `n`th `g`-position, ordered increasingly (Section 3). -/
def lowerPosition (g n : ℕ) : ℕ :=
  Nat.nth (fun a ↦ ∃ b ≥ a, grundy a b = g) n

/-- The larger coordinate paired with the `n`th smaller coordinate (Section 3). -/
def upperPosition (g n : ℕ) : ℕ :=
  sInf {b : ℕ | lowerPosition g n ≤ b ∧ grundy (lowerPosition g n) b = g}

/-- **Conjecture 18**. For every Sprague-Grundy value, the ratio of the larger to the smaller
coordinate of its ordered positions converges to the golden ratio. -/
theorem conjecture_18 (g : ℕ) :
    Filter.Tendsto (fun n ↦ (upperPosition g n : ℝ) / (lowerPosition g n : ℝ))
      Filter.atTop (𝓝 ((1 + √5) / 2)) := by
  sorry

end Jiao2013Sprague
