import Mathlib

/-!
# Geometric-progression-free sets over quadratic number fields

Authors: Andrew Best, Karen Huan, Nathan McNew, Steven J. Miller, Jasmine Powell,
Kimsy Tor, and Madeleine Weinstein.
Origin: [Williams College SMALL REU 2014](https://www.nathanmcnew.com/math.html).
Reference: A. Best, K. Huan, N. McNew, S. J. Miller, J. Powell, K. Tor, and M. Weinstein,
*Geometric-progression-free sets over quadratic number fields*, Proc. Roy. Soc. Edinburgh Sect. A
**147** (2017), 245-262; doi:10.1017/S030821051600010X.
-/

noncomputable section

namespace Best2017Geometric

open scoped NumberField
open scoped Topology
open Finset

open scoped Classical in
/-- The greedy ideal set (Section 3), via the prime-exponent characterization in the proof of
Theorem 3.6 and the ternary description of `A*_3` in Section 2. -/
def greedyIdeals (K : Type*) [Field K] [NumberField K] : Set (Ideal (𝓞 K)) :=
  {I | I ≠ 0 ∧ ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ 0 →
    2 ∉ Nat.digits 3 (factorization I P)}

/-- Asymptotic density among nonzero integral ideals ordered by absolute norm
(Definition 3.2). -/
def HasIdealDensity (K : Type*) [Field K] [NumberField K]
    (A : Set (Ideal (𝓞 K))) (d : ℝ) : Prop := by
  classical
  exact Filter.Tendsto (fun n : ℕ ↦
    let B := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).toFinset.erase 0
    ((#{I ∈ B | I ∈ A} : ℝ) / (#B : ℝ)))
    Filter.atTop (𝓝 d)

/-- **Question 5.1** (pp. 259-260). In every quadratic number field, some set of integral ideals
free of three-term geometric progressions has asymptotic density strictly exceeding that of the
greedy set.

Ratios are nonzero nonunit integral ideals, not fractional ideals, and density is a limit, not a
limsup. -/
theorem question_5_1 (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    ∃ (A : Set (Ideal (𝓞 K))) (d g : ℝ),
      0 ∉ A ∧
      (∀ I R : Ideal (𝓞 K), I ≠ 0 → R ≠ 0 → R ≠ 1 →
        I ∈ A → I * R ∈ A → I * R ^ 2 ∉ A) ∧
      HasIdealDensity K A d ∧ HasIdealDensity K (greedyIdeals K) g ∧ g < d := by
  sorry

end Best2017Geometric
