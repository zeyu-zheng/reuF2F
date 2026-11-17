import Mathlib

/-!
# Jacobi-Trudi determinants over finite fields

Authors: Ben Anzis, Shuli Chen, Yibo Gao, Jesse Kim, Zhaoqi Li, and Rebecca Patrias.
Origin: [University of Minnesota Twin Cities REU
2016](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: B. Anzis, S. Chen, Y. Gao, J. Kim, Z. Li, and R. Patrias, *Jacobi-Trudi determinants
over finite fields*, Ann. Comb. **22** (2018), 447-489; arXiv:1611.00216v1.
-/

namespace Anzis2018Jacobi

/-- The Jacobi-Trudi matrix, with `h` listing the values of `h_1, h_2, ...` (Definition 2.3).
Entries beyond the supplied finite list are zero. -/
def jacobiTrudi {R : Type*} [CommRing R] (lam : YoungDiagram) (h : List R) :
    Matrix (Fin (lam.colLen 0)) (Fin (lam.colLen 0)) R :=
  fun i j ↦
    let m : ℤ := (lam.rowLen i : ℤ) - (i.val : ℤ) + (j.val : ℤ)
    if m < 0 then 0 else if m = 0 then 1 else h.getD (m.toNat - 1) 0

/-- **Conjecture 5.10** (p. 15). The vanishing probability of a Schur function under uniform
finite-field specialization is at most the singularity probability of a uniformly random square
matrix with as many rows as the partition. -/
theorem conjecture_5_10 (K : Type*) [Field K] [Fintype K]
    (lam : YoungDiagram) (hlam : lam.cells.Nonempty) :
    (Nat.card {x : Fin (lam.rowLen 0 + lam.colLen 0 - 1) → K //
        (jacobiTrudi lam (List.ofFn x)).det = 0} : ℚ) /
        (Fintype.card K : ℚ) ^ (lam.rowLen 0 + lam.colLen 0 - 1) ≤
      1 - (Nat.card (Matrix.GeneralLinearGroup (Fin (lam.colLen 0)) K) : ℚ) /
        (Fintype.card K : ℚ) ^ (lam.colLen 0 ^ 2) := by
  sorry

end Anzis2018Jacobi
