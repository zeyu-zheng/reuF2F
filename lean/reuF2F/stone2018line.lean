import Mathlib

/-!
# Line Complexity Asymptotics of Polynomial Cellular Automata

Author: Bertrand Stone.
Origin: [MIT UROP+ 2015](https://math.mit.edu/research/undergraduate/urop-plus/papers.html).
Reference: B. Stone, *Line Complexity Asymptotics of Polynomial Cellular Automata*,
arXiv:1604.02753v2.
-/

noncomputable section

namespace Stone2018Line

open Polynomial

/-- The number of distinct length-`k` blocks occurring in any row of the integer-indexed
automaton with initial state `1` and transition rule `T` (Sections 1-2). -/
def lineComplexity (T : Polynomial (ZMod 2)) (k : ℕ) : ℕ :=
  Nat.card { b : Fin k → ZMod 2 //
    ∃ t : ℕ, ∃ j : ℤ,
      ∀ i : Fin k, b i = (T ^ t).toLaurent.coeff (j + (i.val : ℤ)) }

/-- **Unnumbered conjecture** (Section 9, p. 30). The rule `1 + x + x ^ 3 + x ^ 4` satisfies
both order-four line-complexity recursions of Theorem 5 with a common constant. -/
theorem section_9_recurrence_conjecture :
    let a := fun k : ℕ ↦
      (lineComplexity (1 + X + X ^ 3 + X ^ 4 : Polynomial (ZMod 2)) k : ℤ)
    ∃ C : ℤ, ∀ᶠ k : ℕ in Filter.atTop,
      a (2 * k) = 2 * a k + 2 * a (k + 2) + C ∧
      a (2 * k + 1) = a k + a (k + 1) + a (k + 2) + a (k + 3) + C := by
  sorry

end Stone2018Line
