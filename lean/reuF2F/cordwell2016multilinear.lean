import Mathlib

/-!
# Multilinear polynomials of small degree evaluated on matrices over a unital algebra

Authors: Katherine Cordwell and George Wang.
Origin: [Kent State University REU
2015](https://www.kent.edu/math/research-experiences-undergraduates).
Reference: K. Cordwell and G. Wang, *Multilinear polynomials of small degree evaluated on
matrices over a unital algebra*, Linear Algebra Appl. **496** (2016), 262--287;
DOI 10.1016/j.laa.2015.12.033.
-/

noncomputable section

namespace Cordwell2016Multilinear

/-- **Conjecture 1** (p. 264). Every traceless matrix over a unital associative algebra is the
sum of two values of each nonzero multilinear polynomial of degree at most one more than the
matrix size.

The coefficient algebra need not be commutative; trace is the diagonal sum in that algebra, and
nonzero means formally nonzero. -/
theorem traceless_sum_two_values
    (K : Type*) [Field K] [CharZero K]
    (R : Type*) [Ring R] [Algebra K R]
    (n : ℕ) {m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) (hnm : m - 1 ≤ n)
    (c : Equiv.Perm (Fin m) → K) :
    let f : FreeAlgebra K (Fin m) :=
      ∑ s : Equiv.Perm (Fin m),
        c s • (List.ofFn (fun i : Fin m ↦ FreeAlgebra.ι K (s i))).prod
    f ≠ 0 →
      ∀ A : Matrix (Fin n) (Fin n) R, Matrix.trace A = 0 →
        ∃ X Y : Fin m → Matrix (Fin n) (Fin n) R,
          (FreeAlgebra.lift K X) f + (FreeAlgebra.lift K Y) f = A := by
  sorry

end Cordwell2016Multilinear
