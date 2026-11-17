import Mathlib

/-!
# Sampling on the Sierpinski Gasket

Authors: Richard Oberlin, Brian Street, and Robert S. Strichartz.
Origin: [Cornell Mathematics REU](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: R. Oberlin, B. Street, and R. S. Strichartz, *Sampling on the Sierpinski Gasket*,
Experiment. Math. **12** (2003), no. 4, 403-418; doi:10.1080/10586458.2003.10504509.
-/

noncomputable section

namespace Oberlin2003Sampling

open Finset

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
/-- The graph Laplacian over finite-level neighbors (1-11). -/
def graphLaplacian (m : ℕ) (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ y ∈ vertices m with (levelGraph m).Adj x y, (u y - u x)

/-- The Kigami Laplacian relation, as a uniform limit of graph Laplacians (1-10). -/
def HasLaplacian (u v : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  ContinuousOn u gasket ∧ ContinuousOn v gasket ∧
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∀ x ∈ vertices m, x ∉ vertices 0 →
        |(3 / 2 : ℝ) * (5 : ℝ) ^ m * graphLaplacian m u x - v x| < ε

/-- The Dirichlet eigenspace `E_λ` for `-Δ`. Functions are extended by zero outside `SG`. -/
def dirichletEigenspace (μ : ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 2) → ℝ) :=
  Submodule.span ℝ {u | HasLaplacian u (fun x ↦ -μ * u x) ∧
    (∀ x ∈ vertices 0, u x = 0) ∧ (∀ x ∉ gasket, u x = 0)}

/-- The space `B_m` of the lowest `card (V_m \ V_0)` Dirichlet eigenfunctions. Eigenspace
multiplicities are counted through cardinal rank. -/
def bandlimited (m : ℕ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin 2) → ℝ) :=
  Submodule.span ℝ {u | ∃ μ > (0 : ℝ),
    u ∈ dirichletEigenspace μ ∧
    Module.rank ℝ ((⨆ t : {a : ℝ // 0 < a ∧ a ≤ μ},
      dirichletEigenspace t.val) :
        Submodule ℝ (EuclideanSpace ℝ (Fin 2) → ℝ)) ≤
      (#(vertices m \ vertices 0) : Cardinal)}

/-- The level-`m` cells, adjacent exactly when two distinct closed cells meet. -/
def cellGraph (m : ℕ) : SimpleGraph {w : List (Fin 3) // w.length = m} where
  Adj v w := v ≠ w ∧
    ((cellMap v.val '' gasket) ∩ (cellMap w.val '' gasket)).Nonempty
  symm := ⟨by
    rintro v w ⟨hne, x, hv, hw⟩
    exact ⟨hne.symm, x, hw, hv⟩⟩
  loopless := ⟨by intro w hw; exact hw.1 rfl⟩

/-- `d_m(x,y)`, the least number of level-`m` cells in a chain joining the points. -/
def cellDistance (m : ℕ) (x y : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  sInf {n | ∃ v w : {w : List (Fin 3) // w.length = m},
    x ∈ cellMap v.val '' gasket ∧ y ∈ cellMap w.val '' gasket ∧
    ∃ p : (cellGraph m).Walk v w, n = p.length + 1}

/-- **Conjecture 3.1** ((3-1), p. 409). The canonical Dirichlet sampling functions have a
uniform exponential bound in level-cell distance.

Positive decay constants are the contextual convention; the spectral cutoff follows p. 406,
correcting p. 405's dimension typo, and the sampling function is characterized existentially,
being unique by the source's interpolation result. -/
theorem sampling_exponential_decay :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ α < 1 ∧
      ∀ m : ℕ, ∀ y ∈ vertices m, y ∉ vertices 0 →
        ∃ ψ ∈ bandlimited m,
          (∀ z ∈ vertices m, z ∉ vertices 0 →
            ψ z = if z = y then 1 else 0) ∧
          ∀ x ∈ gasket, |ψ x| ≤ c * α ^ cellDistance m x y := by sorry

end Oberlin2003Sampling
