import Mathlib

/-!
# Generic classification and asymptotic enumeration of dope matrices

Author: Ankit Bisain.
Origin: [University of Minnesota Duluth REU 2022](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: A. Bisain, *Generic classification and asymptotic enumeration of dope matrices*,
arXiv:2209.13811v1.
-/

open Filter
open scoped Asymptotics

namespace Bisain2024Generic

/-- The dope matrices: zero patterns of a degree-`n` complex polynomial and its derivatives at
`m` ordered distinct complex numbers (Section 1). -/
def dopeMatrices (m n : ℕ) : Set (Matrix (Fin m) (Fin (n + 1)) (Fin 2)) :=
  {M | ∃ p : Polynomial ℂ, p.degree = (n : WithBot ℕ) ∧
    ∃ z : Fin m → ℂ, Function.Injective z ∧
      ∀ i j, M i j = 1 ↔ ((Polynomial.derivative^[j.val]) p).eval (z i) = 0}

/-- **Conjecture 5.1**. The logarithm of the number of dope matrices has the proposed sharp
asymptotic throughout `1 < m ≤ (n ^ 2 + n) / 2` as `n` tends to infinity. -/
theorem conjecture_5_1 (m n : ℕ → ℕ) (hm : ∀ t, 1 < m t)
    (hmn : ∀ t, 2 * m t ≤ n t ^ 2 + n t) (hn : Tendsto n atTop atTop) :
    (fun t ↦ Real.log ((dopeMatrices (m t) (n t)).ncard : ℝ)) ~[atTop]
      (fun t ↦ Real.log
        (((n t ^ m t * (m t * n t).choose (n t) : ℕ) : ℝ))) := by
  sorry

end Bisain2024Generic
