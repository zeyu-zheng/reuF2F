import Mathlib

/-!
# Bijections of Strictly Convex Sets and Closed Convex Projective Surfaces that Preserve Complete Geodesics

Author: Drimik Roy Chowdhury.
Origin: [University of Michigan REU
2021](https://prod.lsa.umich.edu/content/dam/math-assets/math-document/reu-documents/ugradreu/2021/D-Chowdhury_REU21-FINAL.pdf).
Reference: D. R. Chowdhury, *Bijections on strictly convex sets and closed convex projective
surfaces that preserve complete geodesics*, preprint (2022); arXiv:2209.04896v1.
-/

noncomputable section

namespace Roy2022Bijections

open Set
open scoped MatrixGroups Pointwise

local notation "E" => EuclideanSpace ℝ (Fin 2)
local notation "RP2" => Projectivization ℝ (Fin 3 → ℝ)

/-- The standard affine chart `x ↦ [1 : x_0 : x_1]` in the real projective plane. -/
def affineChart (x : E) : RP2 :=
  Projectivization.mk ℝ ![1, x 0, x 1] (by
    intro h
    have h₀ := congrFun h 0
    norm_num at h₀)

/-- The quotient topology on the real projective plane. -/
scoped instance projectiveTopology : TopologicalSpace RP2 := by
  unfold Projectivization
  infer_instance

/-- The quotient topology `GL(3, ℝ) / Z(GL(3, ℝ))` on `PGL(3, ℝ)`. -/
scoped instance projectiveGroupTopology : TopologicalSpace PGL(3, ℝ) := by
  unfold Matrix.ProjGenLinGroup
  infer_instance

/-- The Hilbert distance, with the source's log-cross-ratio normalization (Definition 2.2). The
boundary endpoints are located as an infimum and a supremum over the chord. -/
def hilbertDistance (Ω : Set E) (x y : E) : ℝ :=
  if x = y then 0 else
    let T : Set ℝ := {t | x + t • (y - x) ∈ Ω}
    let a := x + sInf T • (y - x)
    let b := x + sSup T • (y - x)
    Real.log (dist a y * dist b x / (dist a x * dist b y))

/-- The orbit quotient of the projective domain by the given subgroup (Definition 4.1). -/
abbrev Surface (Ω : Set E)
    (Γ : Subgroup (MulAction.stabilizer PGL(3, ℝ) (affineChart '' Ω))) :=
  Quotient (MulAction.orbitRel Γ (affineChart '' Ω))

/-- The quotient projection, with affine points represented in the projective chart. -/
def projection (Ω : Set E)
    (Γ : Subgroup (MulAction.stabilizer PGL(3, ℝ) (affineChart '' Ω)))
    (x : Ω) : Surface Ω Γ :=
  Quotient.mk (MulAction.orbitRel Γ (affineChart '' Ω))
    ⟨affineChart x, ⟨x, x.property, rfl⟩⟩

/-- The induced Hilbert distance on the quotient, as the infimum over all lifts. By projective
invariance this equals the source's infimum over deck translates of one lift. -/
def quotientHilbertDistance (Ω : Set E)
    (Γ : Subgroup (MulAction.stabilizer PGL(3, ℝ) (affineChart '' Ω)))
    (p q : Surface Ω Γ) : ℝ :=
  sInf {r | ∃ x y : Ω, projection Ω Γ x = p ∧
    projection Ω Γ y = q ∧ r = hilbertDistance Ω x y}

/-- A complete geodesic, as the projection of the intersection of the domain with a line. -/
def completeGeodesic (Ω : Set E)
    (Γ : Subgroup (MulAction.stabilizer PGL(3, ℝ) (affineChart '' Ω)))
    (L : AffineSubspace ℝ E) : Set (Surface Ω Γ) :=
  projection Ω Γ '' {x : Ω | (x : E) ∈ L}

/-- **Unnumbered conjecture** (Introduction, p. 2; specified in Section 4). Every bijection of
the surface carrying each complete geodesic onto a complete geodesic preserves the quotient
Hilbert distance.

No continuity, orientability or surjectivity on the geodesic family is assumed. -/
theorem complete_geodesic_bijection_preserves_hilbert_distance
    (Ω : Set E) (hNonempty : Ω.Nonempty) (hOpen : IsOpen Ω)
    (hBounded : Bornology.IsBounded Ω) (hConvex : Convex ℝ Ω)
    (hStrict : ∀ a ∈ frontier Ω, ∀ b ∈ frontier Ω,
      segment ℝ a b ⊆ frontier Ω → a = b)
    (Γ : Subgroup (MulAction.stabilizer PGL(3, ℝ) (affineChart '' Ω)))
    [DiscreteTopology Γ]
    (hFree : ∀ (g : Γ) (x : affineChart '' Ω), g • x = x → g = 1)
    [ProperlyDiscontinuousSMul Γ (affineChart '' Ω)]
    [CompactSpace (Surface Ω Γ)]
    (f : Surface Ω Γ → Surface Ω Γ) (hf : Function.Bijective f)
    (hGeodesics : ∀ L : AffineSubspace ℝ E, Module.finrank ℝ L.direction = 1 →
      (∃ x : Ω, (x : E) ∈ L) →
      ∃ L' : AffineSubspace ℝ E, Module.finrank ℝ L'.direction = 1 ∧
        (∃ x : Ω, (x : E) ∈ L') ∧
        f '' completeGeodesic Ω Γ L = completeGeodesic Ω Γ L')
    (p q : Surface Ω Γ) :
    quotientHilbertDistance Ω Γ (f p) (f q) = quotientHilbertDistance Ω Γ p q := by
  sorry

end Roy2022Bijections
