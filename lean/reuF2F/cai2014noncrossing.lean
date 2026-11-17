import Mathlib

/-!
# Noncrossing Monochromatic Subtrees and Staircases in 0-1 Matrices

Authors: Siyuan Cai, Gillian Grindstaff, Andras Gyarfas, and Warren Shull.
Origin: [Budapest Semesters in Mathematics 2012](https://www.bsmath.hu/staircasefinal.pdf).
Reference: S. Cai, G. Grindstaff, A. Gyarfas, and W. Shull, *Noncrossing monochromatic subtrees
and staircases in 0-1 matrices*, J. Discrete Math. (2014), Article 731519, 5 pp.;
doi:10.1155/2014/731519.
-/

namespace Cai2014Noncrossing

/-- A homogeneous staircase: it moves strictly right within a row or strictly down within a
column, and all its entries have one common value (Section 1). -/
def IsHomogeneousStaircase {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool)
    (s : List (Fin n × Fin n)) : Prop :=
  (∃ b : Bool, ∀ p ∈ s, A p.1 p.2 = b) ∧
    s.IsChain (fun p q ↦
      (p.1 = q.1 ∧ p.2 < q.2) ∨ (p.2 = q.2 ∧ p.1 < q.1))

/-- **Conjecture 8** (manuscript Conjecture 2). Every `n × n` binary matrix contains a homogeneous
staircase with at least `n - 1` entries.

The stronger two-color sum conjecture, withdrawn in the published article, is not asserted. -/
theorem conjecture_8 {n : ℕ} (A : Matrix (Fin n) (Fin n) Bool) :
    ∃ s : List (Fin n × Fin n), IsHomogeneousStaircase A s ∧ n - 1 ≤ s.length := by
  sorry

end Cai2014Noncrossing
