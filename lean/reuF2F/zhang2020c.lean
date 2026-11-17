import Mathlib

/-!
# C-(k,l)-Sum-Free Sets

Author: Rachel Zhang.
Origin: [University of Minnesota Duluth REU 2019](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: R. Zhang, *C-(k,l)-Sum-Free Sets*, arXiv:2001.00327v3.
-/

namespace Zhang2020C

open scoped Pointwise

/-- The maximum cardinality `mu^C_{k,l}` of a noisy sum-free set (Section 1). -/
def noisySumFreeMaximum (n : ℕ+) (C : Finset (ZMod (n : ℕ))) (k l : ℕ) : ℕ :=
  ({A | Disjoint (k • A + (k - 1) • C) (l • A + (l - 1) • C)} :
    Finset (Finset (ZMod (n : ℕ)))).sup Finset.card

/-- **Conjecture 5.1**. Interval noise has the conjectured exact maximum sum-free cardinality for
every modulus and pair of summand counts. -/
theorem conjecture_5_1 (n : ℕ+) (k l c : ℕ) (hl : 1 ≤ l) (hkl : l < k)
    (hc : 2 ≤ c) :
    let C : Finset (ZMod (n : ℕ)) := (Finset.range c).image fun i : ℕ ↦ (i : ZMod (n : ℕ))
    let χ : ℤ := ((n : ℤ) + 2 * ((c : ℤ) - 2)) / ((k : ℤ) + l) - ((c : ℤ) - 2)
    let r : ℤ := (-(k : ℤ) * χ - ((k : ℤ) - 1) * ((c : ℤ) - 2)) %
      (Nat.gcd (n : ℕ) (k - l) : ℤ)
    (noisySumFreeMaximum n C k l : ℤ) =
      max 0 (((n : ℤ) + 2 * ((c : ℤ) - 2) - r) / ((k : ℤ) + l) - ((c : ℤ) - 2)) := by
  sorry

end Zhang2020C
