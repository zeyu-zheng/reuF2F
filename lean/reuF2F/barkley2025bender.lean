import Mathlib

/-!
# Bender-Knuth Billiards in Coxeter Groups

Authors: Grant Barkley, Colin Defant, Eliot Hodges, Noah Kravitz, and Mitchell Lee.
Origin: [University of Minnesota Duluth REU 2023](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: G. Barkley, C. Defant, E. Hodges, N. Kravitz, and M. Lee, *Bender-Knuth Billiards in
Coxeter Groups*, Forum Math. Sigma **13** (2025), e7, 1-55; arXiv:2401.17360v3.
-/

namespace Barkley2025Bender

/-- A convex subset: it contains every element lying on a shortest path in the left Cayley
graph between two of its elements (p. 4, Remark 1.1).

Lying on a shortest path is encoded as additivity of length in the simple generators. -/
def CoxeterConvex {n : ℕ} {M : CoxeterMatrix (Fin n)} (L : Set M.Group) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, ∀ z : M.Group,
    M.toCoxeterSystem.length (y * x⁻¹) =
      M.toCoxeterSystem.length (z * x⁻¹) + M.toCoxeterSystem.length (y * z⁻¹) → z ∈ L

open scoped Classical in
/-- The noninvertible Bender-Knuth toggle `τ_i` with respect to `L` (Definition 1.2).

It is encoded through the right-inversion identity (10): `u` stays fixed exactly when all of `L`
lies on the same side of the separating wall as `u`. -/
noncomputable def toggle {n : ℕ} {M : CoxeterMatrix (Fin n)} (L : Set M.Group) (i : Fin n)
    (u : M.Group) : M.Group :=
  if ∀ v ∈ L, ¬M.toCoxeterSystem.IsRightDescent (v * u⁻¹) i then u else M.simple i * u

/-- The billiards map `Pro_c`: one round applying each toggle once, in the given order
(Definition 1.6). -/
noncomputable def promotion {n : ℕ} {M : CoxeterMatrix (Fin n)} (L : Set M.Group)
    (order : Equiv.Perm (Fin n)) (u : M.Group) : M.Group :=
  (List.finRange n).foldl (fun w j ↦ toggle L (order j) w) u

/-- A futuristic Coxeter element: every nonempty convex set is heavy, that is, contains every
periodic point of `Pro_c` (Definitions 1.6 and 1.9).

The Coxeter element is encoded by the order in which the simple generators are toggled. -/
def Futuristic {n : ℕ} (M : CoxeterMatrix (Fin n)) (order : Equiv.Perm (Fin n)) : Prop :=
  ∀ L : Set M.Group, L.Nonempty → CoxeterConvex L →
    Function.periodicPts (promotion L order) ⊆ L

/-- **Question 12.1** (Section 12.1, arXiv v3 p. 48). There is a contemporary Coxeter group:
one with a futuristic and a non-futuristic Coxeter element.

All finite ranks and all Coxeter labels, including `∞` (matrix entry zero), are allowed. -/
theorem question_12_1 :
    ∃ (n : ℕ) (M : CoxeterMatrix (Fin n)) (future other : Equiv.Perm (Fin n)),
      Futuristic M future ∧ ¬Futuristic M other := by
  sorry

end Barkley2025Bender
