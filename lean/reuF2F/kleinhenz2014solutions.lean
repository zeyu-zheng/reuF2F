import Mathlib

/-!
# Solutions to the Nonlinear Schrodinger Equation in Hyperbolic Space

Author: Peter Kleinhenz.
Origin: [MIT SPUR 2014](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: P. Kleinhenz, *Solutions to the Nonlinear Schrodinger Equation in Hyperbolic Space*,
SPUR final report (2014).
-/

noncomputable section

namespace Kleinhenz2014Solutions

open MeasureTheory FourierTransform Filter
open scoped SchwartzMap LineDeriv Laplacian Topology ENNReal Real

/-- Radial hyperbolic energy data represented by the unitary conjugate
`w(r) = (sinh r / r) u(r)` and its genuine weak Euclidean derivatives. -/
structure RadialEnergy where
  /-- The radial conjugate function `w`. -/
  value : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))
  /-- The weak partial derivatives of `w`. -/
  gradient : Fin 3 → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))
  weak_derivative : ∀ j, (gradient j : 𝓢'((EuclideanSpace ℝ (Fin 3)), ℂ)) =
    ∂_{EuclideanSpace.single j (1 : ℝ)} (value : 𝓢'((EuclideanSpace ℝ (Fin 3)), ℂ))
  radial : ∀ A : (EuclideanSpace ℝ (Fin 3)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 3)),
    (fun x ↦ value (A x)) =ᵐ[volume] value

instance : TopologicalSpace RadialEnergy :=
  TopologicalSpace.induced (fun u : RadialEnergy ↦ (u.value, u.gradient)) inferInstance

/-- The hyperbolic focusing energy in unitary radial coordinates (source (1.2)). -/
def energy (u : RadialEnergy) : ℝ :=
  let ρ : EuclideanSpace ℝ (Fin 3) → ℝ := fun x ↦
    if ‖x‖ = 0 then 1 else ‖x‖ / Real.sinh ‖x‖
  (‖u.value‖ ^ 2 + ∑ j, ‖u.gradient j‖ ^ 2) / 2 -
    (∫ x : EuclideanSpace ℝ (Fin 3), ρ x ^ 4 * ‖u.value x‖ ^ 6) / 6

/-- The Euclidean ground state (Theorem 1.2). -/
def groundState (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (√(1 + ‖x‖ ^ 2 / 3))⁻¹

/-- The linear hyperbolic Schrodinger flow after radial conjugation. It is defined on all of
`L2` by its exact spectral multiplier. -/
def linearFlow (t : ℝ) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
  let phase : EuclideanSpace ℝ (Fin 3) → ℂ := fun ξ ↦
    Complex.exp (-Complex.I * (t : ℂ) *
      ((1 + (2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ))
  let hp : MemLp phase ∞ volume := by
    apply memLp_top_of_bound (μ := volume) (C := 1)
    · apply Continuous.aestronglyMeasurable
      dsimp [phase]
      fun_prop
    · filter_upwards [] with ξ
      simp only [phase, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
        Complex.I_re, Complex.I_im, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      norm_num
  𝓕⁻ ((hp.toLp phase) • (𝓕 f))

/-- **Conjecture 1.4**. Every radial hyperbolic energy datum below both Euclidean ground-state
thresholds has a global focusing solution scattering in both time directions.

The statement uses the unitary radial coordinates `w(r) = (sinh r / r) u(r)`. -/
theorem conjecture_1_4 (u₀ : RadialEnergy)
    (henergy : energy u₀ <
      (∫ x : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ groundState x‖ ^ 2) / 2 -
      (∫ x : EuclideanSpace ℝ (Fin 3), |groundState x| ^ 6) / 6)
    (hgradient : ‖u₀.value‖ ^ 2 + ∑ j, ‖u₀.gradient j‖ ^ 2 <
      ∫ x : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ groundState x‖ ^ 2) :
    let ρ : EuclideanSpace ℝ (Fin 3) → ℝ := fun x ↦
      if ‖x‖ = 0 then 1 else ‖x‖ / Real.sinh ‖x‖
    ∃ u : C(ℝ, RadialEnergy), u 0 = u₀ ∧
      (∃ v : ℝ × (EuclideanSpace ℝ (Fin 3)) → ℂ,
        AEStronglyMeasurable v (volume.prod volume) ∧
        (∀ t : ℝ, (fun x ↦ v (t, x)) =ᵐ[volume] (u t).value) ∧
        ∀ a b : ℝ, a ≤ b →
          (∫⁻ t in Set.Icc a b, ∫⁻ x : EuclideanSpace ℝ (Fin 3),
            ENNReal.ofReal (ρ x ^ 8 * ‖v (t, x)‖ ^ 10)) < ∞) ∧
      (∀ (t : ℝ) (φ : 𝓢((EuclideanSpace ℝ (Fin 3)), ℂ)),
        Integrable (fun x : EuclideanSpace ℝ (Fin 3) ↦
          (u t).value x * ((Δ φ) x - φ x) +
          (ρ x ^ 4 : ℂ) * (‖(u t).value x‖ ^ 4 : ℂ) *
            (u t).value x * φ x) volume ∧
        HasDerivAt (fun s : ℝ ↦ ∫ x : EuclideanSpace ℝ (Fin 3), (u s).value x * φ x)
          (Complex.I * ∫ x : EuclideanSpace ℝ (Fin 3),
            (u t).value x * ((Δ φ) x - φ x) +
            (ρ x ^ 4 : ℂ) * (‖(u t).value x‖ ^ 4 : ℂ) *
              (u t).value x * φ x) t) ∧
      ∃ uPlus uMinus : RadialEnergy,
        Tendsto (fun t : ℝ ↦
          ‖(u t).value - linearFlow t uPlus.value‖ ^ 2 +
          ∑ j, ‖(u t).gradient j - linearFlow t (uPlus.gradient j)‖ ^ 2)
          atTop (𝓝 0) ∧
        Tendsto (fun t : ℝ ↦
          ‖(u t).value - linearFlow t uMinus.value‖ ^ 2 +
          ∑ j, ‖(u t).gradient j - linearFlow t (uMinus.gradient j)‖ ^ 2)
          atBot (𝓝 0) := by
  sorry

end Kleinhenz2014Solutions
