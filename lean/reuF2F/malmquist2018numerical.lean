import Mathlib

/-!
# Numerical integration for fractal measures

Authors: Jens Malmquist and Robert S. Strichartz.
Origin: [Cornell Mathematics REU](https://pi.math.cornell.edu/~jensmalmquist/).
Reference: J. Malmquist and R. S. Strichartz, *Numerical integration for fractal measures*,
J. Fractal Geom.; doi:10.4171/JFG/60; arXiv:1606.02773v3 (2018), 50 pp.
-/

noncomputable section

namespace Malmquist2018Numerical

/-- The ordered equilateral boundary vertices `q0, q1, q2`. -/
def boundary (i : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if i = 0 then WithLp.toLp 2 ![0, 0]
  else if i = 1 then WithLp.toLp 2 ![1, 0]
  else WithLp.toLp 2 ![(1 : ℝ) / 2, √3 / 2]

/-- The contraction `F_i(x) = (x + q_i) / 2`. -/
def contraction (i : Fin 3) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 / 2 : ℝ) • (x + boundary i)

/-- The cell map `F_w`, with the first letter outermost. -/
def cellMap (w : List (Fin 3)) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  w.foldr contraction x

/-- The vertex sets `V_m`. -/
def vertices : ℕ → Finset (EuclideanSpace ℝ (Fin 2))
  | 0 => Finset.univ.image boundary
  | m + 1 => Finset.univ.biUnion fun i ↦ (vertices m).image (contraction i)

/-- The standard gasket, the closure of all finite-level vertices. -/
def gasket : Set (EuclideanSpace ℝ (Fin 2)) :=
  closure (⋃ m : ℕ, (vertices m : Set (EuclideanSpace ℝ (Fin 2))))

/-- The level-`m` graph: distinct corners of the same level-`m` cell are adjacent. -/
def levelGraph (m : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := x ≠ y ∧ ∃ w : List (Fin 3), w.length = m ∧
    ∃ i k : Fin 3, x = cellMap w (boundary i) ∧ y = cellMap w (boundary k)
  symm := ⟨by
    rintro x y ⟨hne, w, hw, i, k, hx, hy⟩
    exact ⟨hne.symm, w, hw, k, i, hy, hx⟩⟩
  loopless := ⟨by intro x hx; exact hx.1 rfl⟩

open scoped Classical in
/-- **Example 3.2** (p. 15). The Dirichlet Green potential for the three boundary vertices and
one first-level midpoint has global maximum `11 / 225`.

The potential is characterized pointwise through the full uniform graph limit away from the four
pinned points, with the standard symmetric measure and Kigami normalization. -/
theorem discrepancy_one_midpoint
    (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hu : ContinuousOn u gasket)
    (hboundary : ∀ i : Fin 3, u (boundary i) = 0)
    (hpinned : u (contraction 0 (boundary 1)) = 0)
    (hpoisson : ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∀ x ∈ vertices m, x ∉ vertices 0 → x ≠ contraction 0 (boundary 1) →
        |(3 / 2 : ℝ) * (5 : ℝ) ^ m *
          ∑ y ∈ vertices m with (levelGraph m).Adj x y, (u y - u x) + 1| < ε) :
    IsGreatest (u '' gasket) (11 / 225 : ℝ) := by
  sorry

end Malmquist2018Numerical
