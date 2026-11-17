import Mathlib

/-!
# Isoperimetric Regions in Gauss Sectors

Authors: Elizabeth Adams, Ivan Corwin, Diana Davis, Michelle Lee, and Regina Visocchi.
Origin: [Williams College SMALL REU 2005](https://web.williams.edu/Mathematics/published.html).
Reference: E. Adams, I. Corwin, D. Davis, M. Lee, and R. Visocchi, *Isoperimetric regions in
Gauss sectors*, Rose-Hulman Undergrad. Math. J. **8** (2007), no. 1, Article 1, 28 pp.;
https://scholar.rose-hulman.edu/rhumj/vol8/iss1/1/.
-/

noncomputable section

namespace Adams2007Isoperimetric

open Set MeasureTheory
open scoped ContDiff symmDiff Real ENNReal

/-- The polar interior of the sector, with distinct angular sheets retained (Definition 2.1).
The physical metric is `dr ^ 2 + r ^ 2 dθ ^ 2`, not the coordinate product norm. -/
def sectorInterior (α : ℝ) : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨Ioi 0 ×ˢ Ioo 0 α, isOpen_Ioi.prod isOpen_Ioo⟩

/-- Gaussian area, including the polar Jacobian and the source normalization (Definition 2.1). -/
def sectorMeasure (α : ℝ) : Measure (ℝ × ℝ) :=
  (volume.withDensity (fun x : ℝ × ℝ ↦
    ENNReal.ofReal (x.1 * Real.exp (-(x.1 ^ 2) / 2) / (2 * π)))).restrict
      (sectorInterior α)

/-- The free-boundary weighted perimeter of a measurable region, as a relative BV flux supremum.
Fields use orthonormal polar components bounded in Euclidean L2 (squares, not the sup norm). -/
def sectorPerimeter (α : ℝ) (E : Set (ℝ × ℝ)) : ℝ≥0∞ :=
  ⨆ (F : TestFunction (sectorInterior α) (ℝ × ℝ) 1)
    (_ : ∀ x, (F x).1 ^ 2 + (F x).2 ^ 2 ≤ 1),
    ENNReal.ofReal (∫ x in E ∩ (sectorInterior α : Set (ℝ × ℝ)),
      (fderiv ℝ (fun y : ℝ × ℝ ↦
        y.1 * Real.exp (-(y.1 ^ 2) / 2) / (2 * π) * (F y).1) x) (1, 0) +
      (fderiv ℝ (fun y : ℝ × ℝ ↦
        Real.exp (-(y.1 ^ 2) / 2) / (2 * π) * (F y).2) x) (0, 1))

/-- A rounded half-edge with real parameter `n = π / α` (Definition 3.2). It is a simple regular
polar arc with signed Definition 2.8 curvature, not the unsigned equation of Proposition 4.1. -/
structure RoundedArc (α : ℝ) where
  angle_pos : 0 < α
  /-- The arc-length parameter interval length of the half-edge. -/
  length : ℝ
  length_pos : 0 < length
  /-- The arc-length parametrisation in polar coordinates (radius, angle). -/
  curve : ℝ → ℝ × ℝ
  smooth : ContDiff ℝ ∞ curve
  radius_pos : ∀ s ∈ Icc 0 length, 0 < (curve s).1
  start_angle : (curve 0).2 = 0
  end_angle : (curve length).2 = α
  interior : ∀ s ∈ Ioo 0 length, 0 < (curve s).2 ∧ (curve s).2 < α
  simple : InjOn curve (Icc 0 length)
  radial_monotone : StrictMonoOn (fun s ↦ (curve s).1) (Icc 0 length) ∨
    StrictAntiOn (fun s ↦ (curve s).1) (Icc 0 length)
  orthogonal :
    deriv (fun s ↦ (curve s).1) 0 = 0 ∧
    deriv (fun s ↦ (curve s).1) length = 0
  consecutive : ∀ s ∈ Ioo 0 length,
    deriv (fun t ↦ (curve t).1) s ≠ 0
  reflected_continuation :
    (∀ s, curve (-s) = ((curve s).1, -(curve s).2)) ∧
    (∀ s, curve (2 * length - s) = ((curve s).1, 2 * α - (curve s).2))
  /-- The constant Definition 2.8 Gauss-weighted curvature of the arc. -/
  curvature : ℝ
  geometry :
    let J := Icc 0 length
    let g := fun s ↦ polarCoord.symm (curve s)
    let v := deriv g
    let a := deriv v
    (∀ s ∈ J,
      (v s).1 ^ 2 + (v s).2 ^ 2 = 1 ∧
      0 ≤ (v s).1 * (a s).2 - (v s).2 * (a s).1 ∧
      (v s).1 * (a s).2 - (v s).2 * (a s).1 -
        (g s).1 * (v s).2 + (g s).2 * (v s).1 = curvature) ∧
    (∃ s ∈ Ioo 0 length, 0 < (v s).1 * (a s).2 - (v s).2 * (a s).1)

/-- The vertex-side component cut off by the rounded half-edge. Strict radial monotonicity
places the seed point below every point of the arc. -/
def RoundedArc.vertexSide {α : ℝ} (C : RoundedArc α) :
    TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨connectedComponentIn
      ((sectorInterior α : Set (ℝ × ℝ)) \ C.curve '' Icc 0 C.length)
      (min (C.curve 0).1 (C.curve C.length).1 / 2, α / 2), by
    apply IsOpen.connectedComponentIn
    exact (sectorInterior α).isOpen.sdiff
      (isCompact_Icc.image C.smooth.continuous).isClosed⟩

/-- **Conjecture 3.3** (pp. 6-7). The full angle-and-mass phase diagram and four-shape
classification of Gaussian free-boundary isoperimetric regions in sectors.

Uniqueness is modulo null sets and sector reflection, with complements at half mass only; ties
assert coexistence, and ray-only phases carry no uniqueness. Approximate numerical thresholds are
existentially quantified. At `α = π / 2`, half-mass circle minimality is asserted without
uniqueness, which is claimed only for `q < a < 1 / 8`. -/
theorem conjecture_3_3 :
    /- The exterior of the centered circular arc (Figure 2, Proposition 3.23). -/
    let circularRegion (α R : ℝ) : Set (ℝ × ℝ) :=
      {x | x ∈ sectorInterior α ∧ R < x.1}

    /- The cap cut off by a ray perpendicular to the lower edge (Proposition 3.19). Only the
    first-quadrant sheet is used, even when `α > 2 * π`. -/
    let perpendicularRayRegion (α h : ℝ) : Set (ℝ × ℝ) :=
      {x | x ∈ sectorInterior α ∧ x.2 < π / 2 ∧
        h < x.1 * Real.cos x.2}

    /- The lower-edge subsector cut off by an origin ray of angle `θ` (Proposition 3.15). -/
    let originRayRegion (α θ : ℝ) : Set (ℝ × ℝ) :=
      {x | x ∈ sectorInterior α ∧ x.2 < θ}
    ∃ β q : ℝ,
      π / 2 < β ∧ β < π ∧ 0 < q ∧ q < 1 / 8 ∧
      ∀ α > (0 : ℝ),
        let U : Set (ℝ × ℝ) := sectorInterior α
        let μ := sectorMeasure α
        let P := sectorPerimeter α
        let M := α / (2 * π)
        let reflect := fun F : Set (ℝ × ℝ) ↦
          {x | x ∈ U ∧ (x.1, α - x.2) ∈ F}
        ∃ c b : ℝ,
          (α < π / 2 → 0 < c ∧ c < M / 2) ∧
          (π / 2 < α ∧ α < β → 0 < b ∧ b < M / 2) ∧
          ∀ A > (0 : ℝ), A < M →
            let a := min A (M - A)
            let fullSide := fun F : Set (ℝ × ℝ) ↦
              if M / 2 < A then U \ F else F
            let minimizing := fun F : Set (ℝ × ℝ) ↦
              NullMeasurableSet F μ ∧ F ⊆ U ∧ μ F = ENNReal.ofReal A ∧
                P F < ⊤ ∧
                ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                  μ E = ENNReal.ofReal A → P F ≤ P E
            let sameShape := fun E F : Set (ℝ × ℝ) ↦
              ∃ reflected complemented : Bool,
                (complemented = true → 2 * A = M) ∧
                μ (E ∆ (if complemented then U \ (if reflected then reflect F else F)
                  else if reflected then reflect F else F)) = 0
            (∀ E : Set (ℝ × ℝ), minimizing E →
              ∃ (F : Set (ℝ × ℝ)) (reflected complemented : Bool),
                ((∃ R > (0 : ℝ), F = circularRegion α R) ∨
                  (∃ C : RoundedArc α, F = (C.vertexSide : Set (ℝ × ℝ))) ∨
                  (π / 2 ≤ α ∧ ∃ h ≥ (0 : ℝ),
                    F = perpendicularRayRegion α h) ∨
                  (∃ θ > (0 : ℝ), θ < α ∧
                    F = originRayRegion α θ)) ∧
                μ (E ∆ (if complemented then U \ (if reflected then reflect F else F)
                  else if reflected then reflect F else F)) = 0) ∧
            ∃ R > (0 : ℝ), M * Real.exp (-(R ^ 2) / 2) = a ∧
              μ (circularRegion α R) = ENNReal.ofReal a ∧
              let circle := fullSide (circularRegion α R)
              if α < π / 2 then
                if a < c then
                  ∃ C : RoundedArc α,
                    μ (U \ (C.vertexSide : Set (ℝ × ℝ))) = ENNReal.ofReal a ∧
                    minimizing (fullSide (U \ (C.vertexSide : Set (ℝ × ℝ)))) ∧
                      ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                        μ E = ENNReal.ofReal A →
                          (P E = P (fullSide (U \ (C.vertexSide : Set (ℝ × ℝ)))) ↔
                            sameShape E (fullSide (U \ (C.vertexSide : Set (ℝ × ℝ)))))
                else if a = c then
                  minimizing circle ∧
                    ∃ C : RoundedArc α,
                      μ (U \ (C.vertexSide : Set (ℝ × ℝ))) = ENNReal.ofReal a ∧
                      minimizing (fullSide (U \ (C.vertexSide : Set (ℝ × ℝ)))) ∧
                        P (fullSide (U \ (C.vertexSide : Set (ℝ × ℝ)))) = P circle
                else
                  minimizing circle ∧
                    ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                      μ E = ENNReal.ofReal A → (P E = P circle ↔ sameShape E circle)
              else if α ≤ π then
                ∃ h ≥ (0 : ℝ),
                  (1 / (2 * √(2 * π))) *
                    (∫ t in Ioi h, Real.exp (-(t ^ 2) / 2)) = a ∧
                  μ (perpendicularRayRegion α h) = ENNReal.ofReal a ∧
                  let ray := fullSide (perpendicularRayRegion α h)
                  if α = π / 2 then
                    if a < q then
                      minimizing ray ∧
                        ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                          μ E = ENNReal.ofReal A → (P E = P ray ↔ sameShape E ray)
                    else if a = q then
                      minimizing circle ∧ minimizing ray ∧ P circle = P ray
                    else
                      minimizing circle ∧
                        (a < 1 / 8 →
                          ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                            μ E = ENNReal.ofReal A →
                              (P E = P circle ↔ sameShape E circle))
                  else if α < β then
                    if a < b then
                      minimizing ray ∧ P ray < P circle
                    else if a = b then
                      minimizing circle ∧ minimizing ray ∧ P circle = P ray
                    else
                      minimizing circle ∧
                        ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                          μ E = ENNReal.ofReal A →
                            (P E = P circle ↔ sameShape E circle)
                  else if α = β then
                    if a = M / 2 then
                      minimizing circle ∧ minimizing ray ∧ P circle = P ray
                    else
                      minimizing ray ∧ P ray < P circle
                  else
                    minimizing ray ∧
                      (α = π →
                        ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                          μ E = ENNReal.ofReal A → (P E = P ray ↔ sameShape E ray))
              else if a ≤ 1 / 4 then
                ∃ h ≥ (0 : ℝ),
                  (1 / (2 * √(2 * π))) *
                    (∫ t in Ioi h, Real.exp (-(t ^ 2) / 2)) = a ∧
                  μ (perpendicularRayRegion α h) = ENNReal.ofReal a ∧
                  (a = 1 / 4 → h = 0) ∧
                  minimizing (fullSide (perpendicularRayRegion α h))
              else
                μ (originRayRegion α (2 * π * a)) = ENNReal.ofReal a ∧
                  minimizing (fullSide (originRayRegion α (2 * π * a))) ∧
                  (a = M / 2 →
                    ∀ E : Set (ℝ × ℝ), NullMeasurableSet E μ → E ⊆ U →
                      μ E = ENNReal.ofReal A →
                        (P E = P (fullSide (originRayRegion α (2 * π * a))) ↔
                          sameShape E (fullSide (originRayRegion α (2 * π * a))))) := by
  sorry

end Adams2007Isoperimetric
