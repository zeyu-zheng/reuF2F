import Mathlib

/-!
# Asymptotics of McKay numbers for S_n

Author: Daniel M. Kane.
Origin: [University of Minnesota Duluth REU
2005](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: D. M. Kane, *Asymptotics of McKay numbers for S_n*, J. Number Theory **124** (2007),
200-228; doi:10.1016/j.jnt.2006.08.011.
-/

noncomputable section

namespace Kane2007Asymptotics

open Finset

/-- The hook number: cells weakly right in the same row or weakly below in the same column,
with the cell itself counted once. -/
def hookLength (lambda : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  #{d ∈ lambda.cells | (d.1 = c.1 ∧ c.2 ≤ d.2) ∨ (d.2 = c.2 ∧ c.1 ≤ d.1)}

/-- The hook product `H(lambda)` over every cell of the diagram. -/
def hookProduct (lambda : YoungDiagram) : ℕ :=
  ∏ c ∈ lambda.cells, hookLength lambda c

/-- The signed difference `a_2(n)` of even- and odd-hook-valuation partition counts, that is,
the sum of `(-1) ^ a p_2(a; n)`. -/
def a2 (n : ℕ) : ℤ :=
  ∑ lambda : Nat.Partition n,
    (-1 : ℤ) ^ padicValNat 2 (hookProduct (YoungDiagram.ofPartition lambda))

/-- **Question 3** (with its expected-answer paragraph). The signed `a_2(n)` has order
`exp (√(c * n / log n))` for a fixed positive `c`.

"On the order of" is read as eventual two-sided positive multiplicative comparison with the
same `c`, without absolute value. -/
theorem question_3 :
    ∃ c A B : ℝ, 0 < c ∧ 0 < A ∧ 0 < B ∧
      ∃ N ≥ (2 : ℕ), ∀ n ≥ N,
        A * Real.exp (√(c * (n : ℝ) / Real.log (n : ℝ))) ≤ (a2 n : ℝ) ∧
        (a2 n : ℝ) ≤ B * Real.exp (√(c * (n : ℝ) / Real.log (n : ℝ))) := by sorry

end Kane2007Asymptotics
