import Mathlib

/-!
# Some conjectures on the maximal height of divisors of x^n - 1

Authors: Nathan C. Ryan, Bryan C. Ward, and Ryan Ward.
Origin: [Bucknell Undergraduate Research Group
2008-2009](https://www.eg.bucknell.edu/~theburg/projects/2008.html).
Reference: N. C. Ryan, B. C. Ward, and R. Ward, *Some conjectures on the maximal height of
divisors of x^n - 1*, Involve **3** (2010), no. 4, 451-457.
-/

noncomputable section

namespace Ryan2010Conjectures

/-- The height of an integral polynomial: its largest absolute coefficient (Section 1). -/
def height (f : Polynomial ℤ) : ℕ :=
  f.support.sup fun k ↦ (f.coeff k).natAbs

/-- The maximal height over integral polynomial divisors of `X ^ n - 1` (Section 1). -/
def maximalDivisorHeight (n : ℕ) : ℕ :=
  sSup {h | ∃ f : Polynomial ℤ, f ∣ Polynomial.X ^ n - 1 ∧ h = height f}

/-- **Conjecture 4.1** (preprint Conjecture 3.3). For every two distinct primes, the maximal
divisor height at their squared product is attained by one of the two specified cyclotomic
products. -/
theorem conjecture_4_1 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    maximalDivisorHeight (p ^ 2 * q ^ 2) =
      max (height (Polynomial.cyclotomic p ℤ * Polynomial.cyclotomic q ℤ *
        Polynomial.cyclotomic (p ^ 2 * q) ℤ * Polynomial.cyclotomic (p * q ^ 2) ℤ))
        (height (Polynomial.cyclotomic p ℤ * Polynomial.cyclotomic q ℤ *
          Polynomial.cyclotomic (p ^ 2) ℤ * Polynomial.cyclotomic (q ^ 2) ℤ)) := by
  sorry

end Ryan2010Conjectures
