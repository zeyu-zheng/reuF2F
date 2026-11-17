import Mathlib

/-!
# Integrality and Thurston Rigidity for Bicritical PCF Polynomials

Authors: Heidi Benham, Alexander Galarraga, Benjamin Hutz, Joey Lupo, Wayne Peng,
and Adam Towsley.
Origin: [Summer@ICERM 2019](https://icerm.brown.edu/program/summer@icerm/si-19).
Reference: H. Benham, A. Galarraga, B. Hutz, J. Lupo, W. Peng, and A. Towsley, *Integrality and
Thurston rigidity for bicritical PCF polynomials*, arXiv:2212.02558.
-/

namespace Benham2023Integrality

/-- An index divisor free prime for `(d, k)` (Definition 8). Here `e` is the exact positive
valuation of `d - r`; since `0` divides no positive `e`, the factor `r = 0` needs no special
case. -/
def IsIndexDivisorFreePrime (d k p : ℕ) : Prop :=
  Nat.Prime p ∧ k < p ∧
    ∃ r e : ℕ,
      r ≤ k ∧ 0 < e ∧ p ^ e ∣ d - r ∧ ¬p ^ (e + 1) ∣ d - r ∧ ¬r ∣ e

/-- **Conjecture 3**. Except for `(27, 3)`, every admissible pair `(d, k)` has a prime `p > k`
dividing one factor `d - r` of `d (d - 1) ⋯ (d - k)` such that `r` does not divide the exact
exponent of `p` in that factor. -/
theorem conjecture_goodprime (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ (d - 1) / 2)
    (hne : ((d, k) : ℕ × ℕ) ≠ (27, 3)) :
    ∃ p : ℕ, IsIndexDivisorFreePrime d k p := by
  sorry

end Benham2023Integrality
