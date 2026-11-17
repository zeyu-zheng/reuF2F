import Mathlib

/-!
# Calculus on the Sierpinski gasket II: point singularities, eigenfunctions, and normal derivatives of the heat kernel

Authors: Nitsan Ben-Gal, Abby Shaw-Krauss, Robert S. Strichartz, and Clint Young.
Origin: [Cornell Mathematics REU](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: N. Ben-Gal, A. Shaw-Krauss, R. S. Strichartz, and C. Young, *Calculus on the
Sierpinski gasket II: point singularities, eigenfunctions, and normal derivatives of the heat
kernel*, Trans. Amer. Math. Soc. **358** (2006), no. 9, 3883-3936;
doi:10.1090/S0002-9947-06-04056-6.
-/

noncomputable section
open scoped Topology
open MeasureTheory Filter

namespace BenGal2006Calculus

/-- The three ordered boundary vertices of the equilateral triangle. -/
def boundary (i : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  if i = 0 then WithLp.toLp 2 ![0, 0]
  else if i = 1 then WithLp.toLp 2 ![1, 0]
  else WithLp.toLp 2 ![(1 : ℝ) / 2, √3 / 2]

/-- The contraction `F_i`. -/
def contraction (i : Fin 3) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  (1 / 2 : ℝ) • (x + boundary i)

/-- The cell map `F_w`, with the first letter outermost. -/
def cellMap (w : List (Fin 3)) (x : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  w.foldr contraction x

/-- The finite vertex sets `V_m`. -/
def vertices : ℕ → Finset (EuclideanSpace ℝ (Fin 2))
  | 0 => Finset.univ.image boundary
  | m + 1 => Finset.univ.biUnion fun i ↦ (vertices m).image (contraction i)

/-- The compact planar gasket, the closure of its finite-level vertices. -/
def gasket : Set (EuclideanSpace ℝ (Fin 2)) :=
  closure (⋃ m : ℕ, (vertices m : Set (EuclideanSpace ℝ (Fin 2))))

/-- The continuous coding map of the three-map iterated function system. -/
def addressMap : C(ℕ → Fin 3, EuclideanSpace ℝ (Fin 2)) where
  toFun a := ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) • boundary (a n)
  continuous_toFun := by
    let C : ℝ := ∑ i : Fin 3, ‖boundary i‖
    have hsum : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) * C) :=
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_right
        ((1 / 2 : ℝ) * C) |>.congr (fun n ↦ by ring)
    apply continuous_tsum (u := fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) * C)
    · intro n
      exact (continuous_const : Continuous (fun _ : ℕ → Fin 3 ↦
        (1 / 2 : ℝ) ^ (n + 1))).smul ((continuous_of_discreteTopology :
        Continuous boundary).comp (continuous_apply n :
          Continuous (fun a : ℕ → Fin 3 ↦ a n)))
    · exact hsum
    · intro n a
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.single_le_sum (fun i _ ↦ norm_nonneg (boundary i)) (Finset.mem_univ _)

/-- The equal-cell-weight self-similar probability measure from (1.3). -/
def gasketMeasure : Measure (EuclideanSpace ℝ (Fin 2)) :=
  (Measure.infinitePi (fun _ : ℕ ↦ (PMF.uniformOfFintype (Fin 3)).toMeasure)).map
    addressMap

/-- The graph whose edges join distinct corners of each `m`-cell. -/
def levelGraph (m : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin 2)) where
  Adj x y := x ≠ y ∧ ∃ w : List (Fin 3), w.length = m ∧
    ∃ i k : Fin 3, x = cellMap w (boundary i) ∧ y = cellMap w (boundary k)
  symm := ⟨by
    rintro x y ⟨hne, w, hw, i, k, hx, hy⟩
    exact ⟨hne.symm, w, hw, k, i, hy, hx⟩⟩
  loopless := ⟨by intro x hx; exact hx.1 rfl⟩

open scoped Classical in
/-- The unrenormalized graph Laplacian on `V_m`. -/
def graphLaplacian (m : ℕ) (u : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ y ∈ vertices m with (levelGraph m).Adj x y, (u y - u x)

/-- The continuous Kigami Laplacian, as a uniform limit of renormalized graph Laplacians. -/
def HasLaplacian (u v : EuclideanSpace ℝ (Fin 2) → ℝ) : Prop :=
  ContinuousOn u gasket ∧ ContinuousOn v gasket ∧
    ∀ ε > (0 : ℝ), ∃ M : ℕ, ∀ m ≥ M,
      ∀ x ∈ vertices m, x ∉ vertices 0 →
        |(3 / 2 : ℝ) * (5 : ℝ) ^ m * graphLaplacian m u x - v x| < ε

/-- The outward normal derivative at `q₀` (1.9). -/
def normalDerivative (u : EuclideanSpace ℝ (Fin 2) → ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (fun m : ℕ ↦ (5 / 3 : ℝ) ^ m *
    (2 * u (boundary 0) - u ((contraction 0)^[m] (boundary 1)) -
      u ((contraction 0)^[m] (boundary 2))))

/-- **Conjecture 9.6(a)** ((9.31), p. 3934). The double outward normal derivative of the
Dirichlet heat kernel has a positive continuous log-5-periodic leading profile.

The kernel is given by a complete real `L²` eigenbasis with full multiplicities, and the
convergent normal series models the mixed kernel normals in (9.27). No least period,
nonconstancy or rate is asserted. -/
theorem conjecture_9_6_a
    (u : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hu : ∀ j, MemLp (u j) 2 gasketMeasure)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 gasketMeasure))
    (hb : ∀ j, b j = (hu j).toLp (u j))
    (μ : ℕ → ℝ) (hμ : ∀ j, 0 < μ j)
    (heigen : ∀ j, HasLaplacian (u j) (fun x ↦ -(μ j) * u j x))
    (hboundary : ∀ j i, u j (boundary i) = 0) :
    ∃ g : ℝ → ℝ, Continuous g ∧ (∀ s, 0 < g s) ∧
      Function.Periodic g (Real.log 5) ∧
      Tendsto (fun t : ℝ ↦
        t ^ (Real.log (25 / 3 : ℝ) / Real.log 5) *
          (∑' j : ℕ, Real.exp (-(μ j) * t) * normalDerivative (u j) ^ 2) -
          g (Real.log (1 / t))) (𝓝[>] 0) (𝓝 0) := by
  sorry

end BenGal2006Calculus
