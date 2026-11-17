import Mathlib

/-!
# Fibonacci Random Generator and Fourier Analysis

Authors: Ethan Bogle, Owen Brass, and Owen Shen.
Origin: [Stanford SURIM
2021](https://surim.stanford.edu/publications/analysis/fibonacci-random-generator-and-fourier-analysis).
Reference: E. Bogle, O. Brass, and O. Shen, *Fibonacci random generator and Fourier analysis*,
Stanford SURIM report (2021).
-/

noncomputable section

namespace Bogle2021Fibonacci

open Filter
open Topology
open Finset

/-- **Conjecture 9.12**. For `m, n ≥ 5`, in the `(m - 1) × (n - 1)` array with entries `r * F_j`,
at least `2 / 7` of the entries lie in `[m / 3, 2m / 3]` modulo `m`, and at least `2 / 5` lie in
`[m / 4, 3m / 4]` modulo `m`.

Both inequalities are cross-multiplied to avoid rounding conventions. -/
theorem conjecture_9_12_fibonacci_array_middle_intervals
    (m n : ℕ) (hm : 5 ≤ m) (hn : 5 ≤ n) :
    2 * ((m - 1) * (n - 1)) ≤
        7 * (#{p ∈ (Finset.Icc 1 (m - 1)).product (Finset.Icc 1 (n - 1)) |
          m ≤ 3 * ((p.1 * Nat.fib p.2) % m) ∧
            3 * ((p.1 * Nat.fib p.2) % m) ≤ 2 * m}) ∧
      2 * ((m - 1) * (n - 1)) ≤
        5 * (#{p ∈ (Finset.Icc 1 (m - 1)).product (Finset.Icc 1 (n - 1)) |
          m ≤ 4 * ((p.1 * Nat.fib p.2) % m) ∧
            4 * ((p.1 * Nat.fib p.2) % m) ≤ 3 * m}) := by
  sorry

end Bogle2021Fibonacci
