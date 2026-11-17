import Mathlib

/-!
# Multiplicative semigroups related to the 3x+1 problem

Author: Ana Caraiani.
Origin: [University of Minnesota Duluth REU 2005](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: A. Caraiani, *Multiplicative semigroups related to the 3x+1 problem*, Adv. Appl. Math.
**45** (2010), no. 3, 373-389; doi:10.1016/j.aam.2010.01.009.
-/

namespace Caraiani2010Multiplicative

/-- **Conjecture 2.1** (Weak qx+1 Conjecture). For every odd prime `q`, the associated semigroup
contains the reciprocal of every positive integer. -/
theorem conjecture_2_1 (q : ℕ) (hq : q.Prime) (hodd : Odd q) (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℚ)) ∈ Subsemigroup.closure
      (insert (1 / 2 : ℚ)
        (Set.range fun k : ℕ ↦
          ((q : ℚ) * k + ((q : ℚ) + 1) / 2) / (2 * (k : ℚ) + 1))) := by
  sorry

end Caraiani2010Multiplicative
