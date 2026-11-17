import Mathlib

/-!
# Calculus on the Sierpinski gasket I: polynomials, exponentials and power series

Authors: Jonathan Needleman, Robert S. Strichartz, Alexander Teplyaev, and Po-Lam Yung.
Origin: [Cornell Mathematics REU
2002](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: J. Needleman, R. S. Strichartz, A. Teplyaev, and P.-L. Yung, *Calculus on the
Sierpinski gasket I: polynomials, exponentials and power series*, J. Funct. Anal. **215**
(2004), 290-340; arXiv:math/0312027.
-/

noncomputable section

namespace Needleman2004Calculus

open scoped Topology

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
/-- The graph Laplacian over finite-level neighbors (1.1). -/
def graphLaplacian (m : ℕ) (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ y ∈ vertices m with (levelGraph m).Adj x y, (u y - u x)

/-- The Kigami Laplacian relation, as a uniform limit of graph Laplacians (1.2). -/
def HasLaplacian (u v : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  ContinuousOn u gasket ∧ ContinuousOn v gasket ∧
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∀ x ∈ vertices m, x ∉ vertices 0 →
        |(3 / 2 : ℝ) * (5 : ℝ) ^ m * graphLaplacian m u x - v x| < ε

/-- **Conjecture 2.10** ((2.36), p. 22). Every first-family monomial based at `q0` is strictly
positive at every other gasket point.

Monomials are characterized as in Definition 2.1 by the Laplacian tower and boundary jets. -/
theorem monomial_positive_away_from_q0 {j : ℕ}
    (u : Fin (j + 2) → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hlap : ∀ r : Fin (j + 1), HasLaplacian (u r.castSucc) (u r.succ))
    (hzero : ∀ x ∈ gasket, u (Fin.last (j + 1)) x = 0)
    (hjets : ∀ r : Fin (j + 1),
      u r.castSucc (boundary 0) = (if r.val = j then 1 else 0) ∧
      Filter.Tendsto (fun m : ℕ ↦ (5 / 3 : ℝ) ^ m *
        (2 * u r.castSucc (boundary 0) -
          u r.castSucc ((contraction 0)^[m] (boundary 1)) -
          u r.castSucc ((contraction 0)^[m] (boundary 2))))
        Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun m : ℕ ↦ (5 : ℝ) ^ m *
        (u r.castSucc ((contraction 0)^[m] (boundary 1)) -
          u r.castSucc ((contraction 0)^[m] (boundary 2))))
        Filter.atTop (𝓝 0))
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ gasket) (hx₀ : x ≠ boundary 0) :
    0 < u ⟨0, by omega⟩ x := by sorry

end Needleman2004Calculus
