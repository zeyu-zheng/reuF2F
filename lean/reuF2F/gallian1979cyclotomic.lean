import Mathlib

/-!
# Cyclotomic polynomials and nonstandard dice

Authors: Joseph A. Gallian and David J. Rusin.
Origin: [University of Minnesota Duluth REU 1977](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: J. A. Gallian and D. J. Rusin, *Cyclotomic polynomials and nonstandard dice*,
Discrete Math. **27** (1979), 245-259.
-/

noncomputable section

namespace Gallian1979Cyclotomic

open Polynomial

/-- The standard die of size `m`, with labels `1, 2, …, m`. -/
def standardDiePolynomial (m : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.Icc 1 m, X ^ k

/-- An `n`-dice game of dice-size `m`, expressed by equality of sum-generating
polynomials with `n` standard dice. -/
def IsNDiceGame (n m : ℕ) (dice : Fin n → ℤ[X]) : Prop :=
  (∀ i : Fin n,
    (∀ k : ℕ, 0 ≤ (dice i).coeff k) ∧ (dice i).coeff 0 = 0 ∧
      (dice i).Monic ∧ (dice i).eval 1 = (m : ℤ)) ∧
    ∏ i : Fin n, dice i = (standardDiePolynomial m) ^ n

/-- `P` is a solution die of dice-size `m` for some nontrivial dice game. -/
def IsSolutionDie (m : ℕ) (P : ℤ[X]) : Prop :=
  ∃ n : ℕ, 1 < n ∧ ∃ dice : Fin n → ℤ[X],
    IsNDiceGame n m dice ∧ ∃ i : Fin n, dice i = P

/-- **Unnumbered conjecture** (after Theorem 6, p. 254). Every label of a solution die of size
`m` is at most `m log m / (2 log 2) + 1`, with equality attainable for powers of two. -/
theorem conjecture_largest_label_log_bound
    (m L : ℕ) (hm : 1 < m) (P : ℤ[X]) (hP : IsSolutionDie m P)
    (hL : 0 < P.coeff L) :
    (L : ℝ) ≤ (m : ℝ) * Real.log (m : ℝ) / (2 * Real.log 2) + 1 := by
  sorry

end Gallian1979Cyclotomic
