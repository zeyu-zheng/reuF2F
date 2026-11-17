import Mathlib

/-!
# (k, lambda)-Anti-Powers and Other Patterns in Words

Author: Amanda Burcroff.
Origin: [University of Minnesota Duluth REU 2018](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: A. Burcroff, *(k, lambda)-Anti-powers and other patterns in words*, Electron. J.
Combin. **25** (2018), no. 4, P4.41.
-/

namespace Burcroff2018K

/-- The least positive length `N(α, k)` forcing a factor that is a `k`-power or a `k`-anti-power
over an alphabet of size `a` (Section 1). -/
noncomputable def N (a k : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∀ w : List (Fin a), w.length = n →
    ∃ m > 0, ∃ blocks : Fin k → List (Fin a),
      (∀ i, (blocks i).length = m) ∧
      (List.ofFn blocks).flatten.IsInfix w ∧
      ((∀ i j, blocks i = blocks j) ∨ Function.Injective blocks)}

/-- **Conjecture 33** (Section 7, p. 16). The equal-order power/anti-power threshold is
independent of the alphabet size, for alphabets of size at least two. -/
theorem conjecture_33 (k a b : ℕ) (hk : 0 < k)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    N a k = N b k := by
  sorry

end Burcroff2018K
