import Mathlib

/-!
# Oblivious Points on Translation Surfaces

Authors: Ian Adelstein, Krish Desai, Anthony Ji, and Grace Zdeblick.
Origin: [Yale SUMRY 2019](https://sumry.yale.edu/past-projects).
Reference: I. Adelstein, K. Desai, A. Ji, and G. Zdeblick, *Oblivious points on translation
surfaces*, arXiv:2008.08494v1 (2020).
-/

namespace Adelstein2022Oblivious

/-- The side identifications of `n` unit squares: the right side of square `i` is glued to the
left side of `horizontal i`, and its top side to the bottom side of `vertical i` (Section 2.1). -/
inductive SquareGluing {n : ℕ} (horizontal vertical : Equiv.Perm (Fin n)) :
    Fin n × unitInterval × unitInterval → Fin n × unitInterval × unitInterval → Prop
  /-- The right side of square `i` is glued to the left side of square `horizontal i`. -/
  | right (i : Fin n) (t : unitInterval) :
      SquareGluing horizontal vertical (i, 1, t) (horizontal i, 0, t)
  /-- The top side of square `i` is glued to the bottom side of square `vertical i`. -/
  | top (i : Fin n) (t : unitInterval) :
      SquareGluing horizontal vertical (i, t, 1) (vertical i, t, 0)

/-- The square-tiled surface glued from these identifications, with the quotient topology
(Section 2.1). -/
abbrev Surface {n : ℕ} (horizontal vertical : Equiv.Perm (Fin n)) : Type :=
  Quot (SquareGluing horizontal vertical)

/-- The projection to the square torus, reducing both local coordinates modulo one
(Remark 2.6). -/
def torusProjection {n : ℕ} (horizontal vertical : Equiv.Perm (Fin n)) :
    C(Surface horizontal vertical, AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) where
  toFun := Quot.lift
    (fun p : Fin n × unitInterval × unitInterval ↦
      ((p.2.1.val : AddCircle (1 : ℝ)), (p.2.2.val : AddCircle (1 : ℝ))))
    (by
      intro a b h
      cases h <;> simp [AddCircle.coe_period])
  continuous_toFun := by
    apply continuous_quot_lift
    fun_prop

/-- A regular point of the surface.

Regularity is encoded as the torus projection being a local homeomorphism at the point, so
regular square vertices are included. -/
def IsRegularPoint {n : ℕ} {horizontal vertical : Equiv.Perm (Fin n)}
    (p : Surface horizontal vertical) : Prop :=
  IsLocalHomeomorphOn (torusProjection horizontal vertical) {p}

/-- An oblivious point: a regular point through which no closed geodesic passes
(Definition 1.1).

A closed geodesic is encoded as an injective loop on the circle of period one through regular
points whose torus projection is a straight motion with nonzero velocity. -/
def IsObliviousPoint {n : ℕ} {horizontal vertical : Equiv.Perm (Fin n)}
    (p : Surface horizontal vertical) : Prop :=
  IsRegularPoint p ∧
    ¬∃ (curve : C(AddCircle (1 : ℝ), Surface horizontal vertical)) (velocity : ℝ × ℝ),
      Function.Injective curve ∧ velocity ≠ 0 ∧ (∀ t, IsRegularPoint (curve t)) ∧
        p ∈ Set.range curve ∧
        ∀ t : ℝ,
          torusProjection horizontal vertical (curve (t : AddCircle (1 : ℝ))) =
            torusProjection horizontal vertical (curve 0) +
              (((t * velocity.1 : ℝ) : AddCircle (1 : ℝ)),
                ((t * velocity.2 : ℝ) : AddCircle (1 : ℝ)))

/-- **Question 6.5** (Section 6, p. 12). For every sufficiently large `n` there is a connected
square-tiled surface with exactly `n` unit squares and an oblivious point.

Connectedness follows the surfaces of Section 4, and all tiles are unit squares as in
Remark 2.6. -/
theorem question_6_5 :
    ∃ N : ℕ, ∀ n ≥ N, ∃ horizontal vertical : Equiv.Perm (Fin n),
      ConnectedSpace (Surface horizontal vertical) ∧
        ∃ p : Surface horizontal vertical, IsObliviousPoint p := by
  sorry

end Adelstein2022Oblivious
