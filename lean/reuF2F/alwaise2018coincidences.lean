import Mathlib

/-!
# Coincidences among skew stable and dual stable Grothendieck polynomials

Authors: Ethan Alwaise, Shuli Chen, Alexander Clifton, Rebecca Patrias, Rohil Prasad, Madeline
Shinners, and Albert Zheng.
Origin: [University of Minnesota Twin Cities REU
2016](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: E. Alwaise, S. Chen, A. Clifton, R. Patrias, R. Prasad, M. Shinners, and A. Zheng,
*Coincidences among skew stable and dual stable Grothendieck polynomials*, Involve **11** (2018),
143-167; doi:10.2140/involve.2018.11.143.
-/

namespace Alwaise2018Coincidences

open Finset

/-- The cells of the ribbon with row-length composition `c`, read bottom to top (Section 2).
Rows are numbered upward and consecutive rows overlap in one column. -/
def ribbonCells {n : ℕ} (c : Composition n) : Finset (ℕ × ℕ) :=
  (Finset.range c.length).biUnion fun r ↦
    (Finset.range (c.blocks.getD r 0)).image fun j ↦
      (r, ((c.blocks.take r).map (fun a ↦ a - 1)).sum + j)

/-- Set-valued tableaux on a diagram with rows numbered upward (Section 2). The alphabet
`1, ..., N` is represented by `Fin N`. -/
abbrev SetValuedTableau (D : Finset (ℕ × ℕ)) (N : ℕ) :=
  {T : D → Finset (Fin N) //
    (∀ b, (T b).Nonempty) ∧
    (∀ b c, b.val.1 = c.val.1 → b.val.2 < c.val.2 →
      ∀ (i : T b) (j : T c), i.val ≤ j.val) ∧
    (∀ b c, b.val.2 = c.val.2 → b.val.1 < c.val.1 →
      ∀ (i : T b) (j : T c), j.val < i.val)}

open scoped Classical in
/-- The stable Grothendieck polynomial in the first `N` variables: a sum over set-valued
tableaux, signed by the number of entries minus cells (Section 2). -/
noncomputable def stableGrothendieck (D : Finset (ℕ × ℕ)) (N : ℕ) :
    MvPolynomial (Fin N) ℤ :=
  ∑ T : SetValuedTableau D N,
    MvPolynomial.C ((-1 : ℤ) ^ ((∑ b : D, #(T.val b)) - #D)) *
      ∏ b : D, ∏ i ∈ T.val b, MvPolynomial.X i

/-- **Conjecture 6.1** (p. 166; preprint Conjecture 5.1). Two ribbons have the same stable
Grothendieck series exactly when they coincide or differ by a 180-degree rotation, which reverses
the row composition.

The sign exponent counts skew cells, following the source's prose and Section 4 identity rather
than the outer-partition size printed in Section 2. -/
theorem conjecture_6_1 {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (a : Composition n) (b : Composition m) :
    (∀ N : ℕ, stableGrothendieck (ribbonCells a) N =
      stableGrothendieck (ribbonCells b) N) ↔
      b.blocks = a.blocks ∨ b.blocks = a.blocks.reverse := by
  sorry

end Alwaise2018Coincidences
