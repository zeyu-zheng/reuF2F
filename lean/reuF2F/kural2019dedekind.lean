import Mathlib

/-!
# Dedekind Sums with Even Denominators

Author: Michael Kural.
Origin: [University of Minnesota Duluth REU 2017](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: M. Kural, *Dedekind sums with even denominators*, J. Number Theory **197** (2019),
106-120.
-/

namespace Kural2019Dedekind

/-- The sawtooth function, with value zero at integers (Definition 1.1). -/
def sawtooth (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

/-- The normalized Dedekind sum `S(a,b) = 12 s(a,b)` (Definition 1.1). -/
def normalizedDedekindSum (a : ℤ) (b : ℕ) : ℚ :=
  12 * ∑ j ∈ Finset.Icc 1 b, sawtooth ((j : ℚ) / b) * sawtooth ((a : ℚ) * j / b)

/-- The residue `h_q(x,y)` (Definition 4.2). The inverse of `y` is chosen by Bezout; off the
coprime domain the value is junk. -/
def h (q : ℕ) (x y : ℤ) : ZMod (q ^ 2 - 1) :=
  let t : ℕ := (x ^ 2 + y ^ 2).toNat
  let a : ℤ := x * Int.gcdA y (t : ℤ)
  (⌊(((q : ℚ) ^ 2 - 1) * a) / t - (q : ℚ) * normalizedDedekindSum (a * q) t⌋ : ℤ)

/-- **Conjecture 4.3**. Every positive-parameter one-variable family `h_q(x + rq, xrq - 1)`
exhausts the prescribed residue subgroup `Gamma_q`. -/
theorem conjecture_4_3 (q r : ℕ) (hq : 2 ≤ q) (hr : 1 ≤ r) :
    {z : ZMod (q ^ 2 - 1) | ∃ x : ℤ,
      Int.gcd (x + (r : ℤ) * q) (x * r * q - 1) = 1 ∧
      Int.gcd (x ^ 2 + 1) q = 1 ∧
      z = h q (x + (r : ℤ) * q) (x * r * q - 1)} =
    {z : ZMod (q ^ 2 - 1) | ∃ s : ZMod (q ^ 2 - 1),
      z = (if IsSquare q then 24 else 12) * s} := by
  sorry

end Kural2019Dedekind
