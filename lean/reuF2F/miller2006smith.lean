import Mathlib

/-!
# Smith invariants of UD and DU linear operators in differential posets

Author: Alexander Miller.
Origin: [University of Minnesota Twin Cities REU
2006](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: A. Miller, *Smith invariants of UD and DU linear operators in differential posets*,
REU report (2006), 13 pp.
-/

noncomputable section

namespace Miller2006Smith

/-- The two differential conditions on the cover relation (Definition 1). The graded, minimum
and local/rank-finiteness conditions are ambient assumptions. -/
def IsDifferential (P : Type*) [PartialOrder P] (r : ℕ) : Prop :=
  (∀ x y : P, x ≠ y →
    Nat.card {z : P // z ⋖ x ∧ z ⋖ y} =
      Nat.card {z : P // x ⋖ z ∧ y ⋖ z}) ∧
  (∀ x : P, Nat.card {y : P // x ⋖ y} =
    Nat.card {y : P // y ⋖ x} + r)

/-- The rank fiber `P_n`, with its inherited labels. -/
abbrev Rank (P : Type*) [PartialOrder P] [GradeOrder ℕ P] (n : ℕ) :=
  {x : P // grade ℕ x = n}

open scoped Classical in
/-- The integral up-incidence matrix in the poset bases (Definition 2). -/
def up (P : Type*) [PartialOrder P] [GradeOrder ℕ P] (n : ℕ) :
    Matrix (Rank P (n + 1)) (Rank P n) ℤ :=
  fun y x ↦ if x.val ⋖ y.val then 1 else 0

/-- **Conjecture 11**. The complete integral Smith factors of every DU operator are the products
of its successive distinct-eigenvalue layers (Definition 7).

Theorem 12 supplies the rank-difference spectrum; the rank-minus-one size is zero. -/
theorem conjecture_11 (P : Type*) [PartialOrder P] [OrderBot P]
    [GradeMinOrder ℕ P] [LocallyFiniteOrder P]
    (hfinite : ∀ n : ℕ, Finite (Rank P n))
    (r : ℕ) (hr : 0 < r) (hP : IsDifferential P r) (n : ℕ) :
    letI : ∀ m : ℕ, Fintype (Rank P m) := fun m ↦ @Fintype.ofFinite _ (hfinite m)
    let p : ℕ → ℕ := fun m ↦ Fintype.card (Rank P m)
    let δ : ℕ → ℤ := fun m ↦ (p m : ℤ) -
      (if m = 0 then 0 else (p (m - 1) : ℤ))
    let d : Fin (p n) → ℤ := fun j ↦
      ∏ i ∈ {i ∈ Finset.range (n + 1) | ((p n - j.val : ℕ) : ℤ) ≤ δ (n - i)},
        (r : ℤ) * (i + 1)
    ∃ L R : Matrix.GeneralLinearGroup (Fin (p n)) ℤ,
      (L : Matrix (Fin (p n)) (Fin (p n)) ℤ) *
          Matrix.of (fun i j ↦ ((up P n).transpose * up P n)
            ((Fintype.equivFin (Rank P n)).symm i) ((Fintype.equivFin (Rank P n)).symm j)) *
        (R : Matrix (Fin (p n)) (Fin (p n)) ℤ) = Matrix.diagonal d := by
  sorry

end Miller2006Smith
