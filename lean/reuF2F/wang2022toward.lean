import Mathlib

/-!
# Toward explicit Hilbert series of quasi-invariant polynomials in characteristic p and q-deformed quasi-invariants

Author: Frank Wang.
Origin: [MIT SPUR 2021](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: F. Wang, *Toward explicit Hilbert series of quasi-invariant polynomials in
characteristic p and q-deformed quasi-invariants*, arXiv:2201.06111v2 (2022).
-/

noncomputable section

namespace Wang2022Toward

open MvPolynomial

/-- The space of `q`-deformed `m`-quasi-invariants (Definition 5.1). -/
def quasiInvariants (n m : ℕ) (q : ℂ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ) where
  carrier := {P | ∀ i j : Fin n, i ≠ j →
    (∏ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ),
      (X i - C (q ^ k) * X j)) ∣ P - rename (Equiv.swap i j) P}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ i j hij
    simpa only [map_add, add_sub_add_comm] using dvd_add (hP i j hij) (hQ i j hij)
  smul_mem' := by
    intro a P hP i j hij
    simpa only [smul_eq_C_mul, map_mul, rename_C, mul_sub] using
      dvd_mul_of_dvd_right (hP i j hij) (C a)

/-- The Hilbert series of the graded spaces of Definition 5.1 (Definition 2.3). -/
def hilbertSeries (n m : ℕ) (q : ℂ) : PowerSeries ℕ :=
  PowerSeries.mk fun d ↦ Module.finrank ℂ
    ↥(quasiInvariants n m q ⊓ homogeneousSubmodule (Fin n) ℂ d)

/-- **Conjecture 5.7**. A change in the Hilbert series forces the stated root order. -/
theorem conjecture_5_7 (n m : ℕ) (hn : 3 ≤ n) (q : ℂ) (hq : q ≠ 0)
    (h : hilbertSeries n m q ≠ hilbertSeries n m 1) :
    ∃ p > 0, IsPrimitiveRoot q p ∧
      ((m : ℚ) * n * ((n : ℚ) - 2) + (n.choose 2 : ℚ)) /
        ((n.choose 2 : ℚ) - 1) ≤ (p : ℚ) ∧ p ≤ m * n := by sorry

end Wang2022Toward
