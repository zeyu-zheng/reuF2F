import Mathlib

/-!
# Flat Cyclotomic Polynomials: A New Approach

Author: Sam Elder.
Origin: [University of Minnesota Duluth REU 2009](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: S. Elder, *Flat cyclotomic polynomials: a new approach*, preprint (2012), 52 pp.;
arXiv:1207.5811v1.
-/

namespace Elder2012Flat

/-- **Conjecture 8**. A cyclotomic polynomial indexed by five distinct odd primes has a
coefficient of absolute value greater than one, so it is not flat. -/
theorem conjecture_8 (p q r s t : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpodd : 2 < p) (hpq : p < q) (hqr : q < r) (hrs : r < s) (hst : s < t) :
    ∃ k : ℕ, 1 < |(Polynomial.cyclotomic (p * q * r * s * t) ℤ).coeff k| := by
  sorry

end Elder2012Flat
