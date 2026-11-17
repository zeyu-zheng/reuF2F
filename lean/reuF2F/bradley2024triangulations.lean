import Mathlib

/-!
# On triangulations of order polytopes for snake posets

Authors: Molly Bradley, Sogol Cyrusian, Aleister Jones, Mario Tomba, and Katherine Tung.
Origin: [University of Minnesota Twin Cities REU
2024](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: M. Bradley, S. Cyrusian, A. Jones, M. Tomba, and K. Tung, *On triangulations of order
polytopes for snake posets*, University of Minnesota REU report (2024).
-/

noncomputable section

namespace Bradley2024Triangulations

/-- The generating cover relations of the snake poset `S_k = P(ε RLRL...)` (Definition 2.13 and
the paragraph after Definition 2.14). -/
def SnakeCover (k : ℕ) (a b : Fin (2 * k + 4)) : Prop :=
  ((a.val = 1 ∨ a.val = 2) ∧ b.val = 0) ∨
  (a.val = 3 ∧ (b.val = 1 ∨ b.val = 2)) ∨
  ∃ j ≥ 1, j ≤ k ∧
    ((a.val = 2 * j + 3 ∧ (b.val = 2 * j + 1 ∨ b.val = 2 * j + 2)) ∨
      (a.val = 2 * j + 2 ∧ b.val = if j = 1 then 2 else 2 * j - 1))

/-- The vertices of the order polytope: characteristic vectors of upper order ideals
(Section 2.2). Monotonicity is checked only on generating covers, which suffices. -/
def orderVertices (k : ℕ) : Set (Fin (2 * k + 4) → ℝ) :=
  {v | (∀ i, v i = 0 ∨ v i = 1) ∧ ∀ a b, SnakeCover k a b → v a ≤ v b}

/-- Triangulations of the order polytope as geometric simplicial complexes (Definition 2.2). They
need not be regular. -/
abbrev SnakeTriangulation (k : ℕ) :=
  {T : Geometry.SimplicialComplex ℝ (Fin (2 * k + 4) → ℝ) //
    T.vertices ⊆ orderVertices k ∧ T.space = convexHull ℝ (orderVertices k)}

/-- The link of a simplex (Definition 2.8). It includes the empty simplex, which Mathlib's
complexes omit but the join in a flip needs. -/
def simplicialLink {k : ℕ} (T : SnakeTriangulation k)
    (s : Finset (Fin (2 * k + 4) → ℝ)) : Set (Finset (Fin (2 * k + 4) → ℝ)) :=
  {t | Disjoint s t ∧ s ∪ t ∈ T.val.faces}

/-- The directed bistellar flip replacing `T_Z^-` by `T_Z^+` (Definition 3.2; circuits and links
as in Definitions 2.6 and 2.9). The direction is fixed by a positive circuit vertex of smallest
filter cardinality (Definition 2.17, Proposition 3.3). -/
def UpFlip {k : ℕ} (T U : SnakeTriangulation k) : Prop :=
  ∃ Z : Finset (Fin (2 * k + 4) → ℝ),
    (Z : Set (Fin (2 * k + 4) → ℝ)) ⊆ orderVertices k ∧
    Minimal (fun C : Finset (Fin (2 * k + 4) → ℝ) ↦
      ¬AffineIndependent ℝ (fun v : C ↦ v.val)) Z ∧
    ∃ c : (Fin (2 * k + 4) → ℝ) → ℝ,
      (∀ v ∈ Z, c v ≠ 0) ∧ (∑ v ∈ Z, c v) = 0 ∧ (∑ v ∈ Z, c v • v) = 0 ∧
      (∃ a ∈ Z, 0 < c a ∧ ∀ b ∈ Z, b ≠ a → (∑ i, a i) < ∑ i, b i) ∧
      let negative := ({v ∈ Z | c v < 0}).image Z.erase
      let positive := ({v ∈ Z | 0 < c v}).image Z.erase
      ∃ L : Set (Finset (Fin (2 * k + 4) → ℝ)),
        (∀ s ∈ negative, s ∈ T.val.faces ∧ simplicialLink T s = L) ∧
        (∀ s ∈ positive, s ∈ U.val.faces ∧ simplicialLink U s = L) ∧
        let patch := fun (D : Finset (Finset (Fin (2 * k + 4) → ℝ)))
            (t : Finset (Fin (2 * k + 4) → ℝ)) ↦
          ∃ s ∈ D, ∃ l ∈ L, t ⊆ s ∪ l
        ∀ t, t ∈ U.val.faces ↔
          t.Nonempty ∧ ((t ∈ T.val.faces ∧ ¬patch negative t) ∨ patch positive t)

/-- **Conjecture 1.5**. For every snake poset, its order-polytope triangulations
form a lattice under the directed-flip order of Definition 3.2. -/
theorem conjecture_1_5 (k : ℕ) :
    ∃ L : Lattice (SnakeTriangulation k),
      ∀ T U, @LE.le (SnakeTriangulation k) L.toLE T U ↔
        Relation.ReflTransGen UpFlip T U := by
  sorry

end Bradley2024Triangulations
