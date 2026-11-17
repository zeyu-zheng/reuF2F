import Mathlib

/-!
# Lower bounds for Betti numbers of monomial ideals

Authors: Adam Boocher and James Seiner.
Origin: [University of Utah REU 2016](https://www.math.utah.edu/undergraduate/reu-archive.php).
Reference: A. Boocher and J. Seiner, *Lower bounds for Betti numbers of monomial ideals*,
J. Algebra **508** (2018), 445-460; doi:10.1016/j.jalgebra.2018.04.013; arXiv:1706.09866v1.
-/

noncomputable section

namespace Boocher2018Lower

open Polynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The Betti number `β_i(S/I) = dim_k Tor_i^S(k, S/I)` (Section 1).

The residue field is an `S`-module by evaluating every variable at zero, and Tor is measured
over `k` by restricting scalars along the constants. -/
def bettiNumber {k : Type u} [Field k] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) (i : ℕ) :
    ℕ :=
  let S := MvPolynomial (Fin n) k
  let residue : ModuleCat.{u} S :=
    (ModuleCat.restrictScalars (MvPolynomial.eval fun _ : Fin n ↦ (0 : k))).obj
      (ModuleCat.of k k)
  let quotient : ModuleCat.{u} S := ModuleCat.of S (S ⧸ I)
  let tor : ModuleCat.{u} S :=
    ((CategoryTheory.Tor (ModuleCat.{u} S) i).obj residue).obj quotient
  Module.finrank k ((ModuleCat.restrictScalars (MvPolynomial.C : k →+* S)).obj tor)

/-- **Question 1.3** (Section 1, arXiv p. 2; journal p. 447). If a homogeneous ideal `I` of
height `c` has total Betti number `2 ^ c + 2 ^ (c - 1)` (a rational power), then the Betti
numbers of `S/I` are one of the two sequences of Theorem 1.1.

The total is the supremum of the finite partial sums in `ℕ∞`, and the condition is stated in
cleared form `2 * ∑ β_i = 3 * 2 ^ c`, so for `c = 0` the required total `3/2` is never attained
(no truncated subtraction occurs). The conclusion is that `c = r + 2` and `β_i` is the
coefficient of `t ^ i` in `(1 + 3t + 2t²)(1 + t) ^ r`, or `c = r + 3` and `β_i` is the
coefficient of `t ^ i` in `(1 + 5t + 5t² + t³)(1 + t) ^ r`, for some `r : ℕ`. -/
theorem question_1_3 {k : Type u} [Field k] {n : ℕ} (c : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (hhom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (hheight : I.height = c)
    (htotal : 2 * (⨆ N, ∑ i ∈ Finset.range N, (bettiNumber I i : ℕ∞)) = 3 * 2 ^ c) :
    (∃ r, c = r + 2 ∧ ∀ i,
      bettiNumber I i = ((1 + 3 * X + 2 * X ^ 2) * (1 + X) ^ r : ℕ[X]).coeff i) ∨
    (∃ r, c = r + 3 ∧ ∀ i,
      bettiNumber I i = ((1 + 5 * X + 5 * X ^ 2 + X ^ 3) * (1 + X) ^ r : ℕ[X]).coeff i) := by
  sorry

end Boocher2018Lower
