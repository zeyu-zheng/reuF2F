import Mathlib

/-!
# Planar Convex Bodies with a Common Directed X-ray

Authors: G. L. Butcher, A. Medin, and D. C. Solmon.
Origin: [Oregon State University REU
2002](https://sites.science.oregonstate.edu/math_reu/proceedings/2002.html).
Reference: G. L. Butcher, A. Medin, and D. C. Solmon, *Planar convex bodies with a common directed
X-ray*, Rend. Istit. Mat. Univ. Trieste **37** (2005), 181-206.
-/

noncomputable section

open scoped Topology Real

namespace Butcher2005Planar

/-- The filled polar region between the near and far functions, including both supporting rays
(pp. 182-183). -/
def radialRegion {α β : ℝ}
    (near far : C(Set.Icc α β, ℝ)) : Set ℂ :=
  {z | ∃ θ : Set.Icc α β, ∃ radius : ℝ,
    0 ≤ radius ∧ near θ ≤ radius ∧ radius ≤ far θ ∧
      z = Complex.polarCoord.symm (radius, (θ : ℝ))}

/-- The family of convex bodies with a common directed X-ray, as continuous near functions whose
region is compact and convex with nonempty interior (pp. 182-183). The zero near function is
allowed, and the topology is uniform convergence. -/
def xrayFamily {α β : ℝ}
    (xray : C(Set.Icc α β, ℝ)) :
    Set C(Set.Icc α β, ℝ) :=
  {near | (∀ θ, 0 ≤ near θ) ∧
    ∃ body : ConvexBody ℂ,
      (interior (body : Set ℂ)).Nonempty ∧
        (body : Set ℂ) = radialRegion near (near + xray)}

/-- A parallel wedge: the near and far sides are parallel straight segments (p. 194). -/
def IsParallelWedge {α β : ℝ} (hab : α < β)
    (near far : C(Set.Icc α β, ℝ)) : Prop :=
  let A := Complex.polarCoord.symm
    (near ⟨α, le_rfl, hab.le⟩, α)
  let B := Complex.polarCoord.symm
    (near ⟨β, hab.le, le_rfl⟩, β)
  let C := Complex.polarCoord.symm
    (far ⟨α, le_rfl, hab.le⟩, α)
  let D := Complex.polarCoord.symm
    (far ⟨β, hab.le, le_rfl⟩, β)
  (Set.range (fun θ : Set.Icc α β ↦
    Complex.polarCoord.symm (near θ, (θ : ℝ))) = segment ℝ A B) ∧
  (Set.range (fun θ : Set.Icc α β ↦
    Complex.polarCoord.symm (far θ, (θ : ℝ))) = segment ℝ C D) ∧
  AffineSubspace.Parallel
    (affineSpan ℝ ({A, B} : Set ℂ))
    (affineSpan ℝ ({C, D} : Set ℂ))

/-- **Open question** (pp. 199-200, with expected answer). Every nonwedge base has a
locally infinite-dimensional common directed-X-ray family in the uniform topology.

Local infinite dimensionality is asserted on a nonempty open subset, the nonvacuous reading of
p. 194; all bases are covered, not only the remaining zero-curvature cases. -/
theorem locally_infinite_dimensional
    (K : ConvexBody ℂ)
    (hinterior : (interior (K : Set ℂ)).Nonempty)
    (hhalfplane : (K : Set ℂ) ⊆ {z | 0 < z.im})
    {α β : ℝ} (hα : 0 < α) (hab : α < β)
    (hβ : β < π)
    (near far : C(Set.Icc α β, ℝ))
    (hnear : ∀ θ, 0 < near θ)
    (horder : ∀ θ, near θ ≤ far θ)
    (hthickness : ∀ θ : Set.Icc α β,
      α < (θ : ℝ) → (θ : ℝ) < β → near θ < far θ)
    (hcarrier : (K : Set ℂ) = radialRegion near far)
    (hnotwedge : ¬IsParallelWedge hab near far)
    (L : xrayFamily (far - near)) (U : Set (xrayFamily (far - near))) (hU : U ∈ 𝓝 L)
    (n : ℕ) :
    ∃ S : Set (xrayFamily (far - near)),
      ∃ V : Set (EuclideanSpace ℝ (Fin n)),
        S ⊆ U ∧ IsOpen V ∧ V.Nonempty ∧ Nonempty (S ≃ₜ V) := by
  sorry

end Butcher2005Planar
