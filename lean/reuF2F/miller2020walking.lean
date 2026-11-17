import Mathlib

/-!
# Walking to Infinity Along Some Number Theory Sequences

Authors: Steven J. Miller, Fei Peng, Tudor Popescu, Joshua M. Siktar,
Nawapan Wattanawanichkul, and the Polymath REU Walking to Infinity Group.
Origin: Polymath Jr. 2020.
Reference: S. J. Miller, F. Peng, T. Popescu, J. M. Siktar, N. Wattanawanichkul, and the
Polymath REU Walking to Infinity Group, *Walking to infinity along some number theory
sequences*, arXiv:2010.14932.
-/

namespace Miller2020Walking

/-- A single right-append step in base `b`, appending a block of exactly `d` digits.
The appended block may have leading zeroes, so its value is some `r < b ^ d`. -/
def IsRightDigitAppend (b : ℕ) (d : ℕ) (n m : ℕ) : Prop :=
  0 < d ∧ ∃ r : ℕ, r < b ^ d ∧ m = n * b ^ d + r

/-- A walk to infinity along primes in base `b`, appending between one and `maxDigits` digits
at each step. `StrictMono w` is implied by the positive append lengths and prime terms. -/
def IsInfinitePrimeWalk (b maxDigits : ℕ) (w : ℕ → ℕ) : Prop :=
  1 < b ∧ 0 < maxDigits ∧ StrictMono w ∧ (∀ i, Nat.Prime (w i)) ∧
    ∀ i, ∃ d > 0, d ≤ maxDigits ∧ IsRightDigitAppend b d (w i) (w (i + 1))

/-- **Conjecture from the conclusion**. There is no walk to infinity along the primes by
appending one digit at a time to the right in base ten. -/
theorem conjecture_no_base_ten_one_digit_prime_walk :
    ¬∃ w : ℕ → ℕ, IsInfinitePrimeWalk 10 1 w := by
  sorry

end Miller2020Walking
