import Mathlib

/-!
# L^p Regularity of Toeplitz Operators on Generalized Hartogs Triangles

Authors: Meijke Balay, Trent Neutgens, Nick Rosen, Nathan Wagner, and Yunus E. Zeytuncu.
Origin: [Polymath Jr. 2020](https://arxiv.org/pdf/2009.07260).
Reference: M. Balay, T. Neutgens, N. Rosen, N. Wagner, and Y. E. Zeytuncu, *L^p Regularity of
Toeplitz Operators on Generalized Hartogs Triangles*, arXiv:2009.07260.
-/

noncomputable section

namespace Balay2022L

open MeasureTheory

/-- The rational generalized Hartogs triangle `H_{m/n}` (Section 1.1). -/
def rationalHartogsTriangle (m n : ℕ) : Set (ℂ × ℂ) :=
  {z | (‖z.1‖ : ℝ) ^ ((m : ℝ) / (n : ℝ)) < ‖z.2‖ ∧ ‖z.2‖ < 1}

/-- The Bergman kernel, summed over the square-integrable Laurent monomials (Section 1.1,
equation (1)). The denominator is their squared `L²` norm for Lebesgue volume. -/
def bergmanKernel (m n : ℕ) (z w : ℂ × ℂ) : ℂ :=
  ∑' α : ℕ × ℤ,
    if -((m : ℤ) + (n : ℤ)) + 1 ≤ (n : ℤ) * (α.1 : ℤ) + (m : ℤ) * α.2 then
      (z.1 ^ α.1 * z.2 ^ α.2) * star (w.1 ^ α.1 * w.2 ^ α.2) /
        ((∫ u : ℂ × ℂ, ‖u.1 ^ α.1 * u.2 ^ α.2‖ ^ 2
          ∂(volume.restrict (rationalHartogsTriangle m n))) : ℂ)
    else 0

open Filter
open scoped Topology ENNReal

/-- **Section 3(3), Further Questions**. There is a bounded symbol on a rational Hartogs triangle
whose Berezin transform tends to zero at every boundary point, but whose Toeplitz operator on
`L²` is not compact, as the authors predict. -/
theorem open_berezin_boundary_vanishing_not_compact_counterexample :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.Coprime m n ∧
      let Ω := rationalHartogsTriangle m n
      let μ : Measure (ℂ × ℂ) := volume.restrict Ω
      ∃ φ : (ℂ × ℂ) → ℂ, MemLp φ ⊤ μ ∧
        ∃ T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
          (∀ f : Lp ℂ 2 μ,
            (T f : (ℂ × ℂ) → ℂ) =ᵐ[μ]
              fun z ↦ ∫ w, bergmanKernel m n z w * φ w * f w ∂μ) ∧
          (∀ z ∈ frontier Ω, Tendsto (fun interior_z ↦
            (∫ w : ℂ × ℂ, φ w * (‖bergmanKernel m n interior_z w‖ ^ 2 : ℝ)
              ∂(volume.restrict (rationalHartogsTriangle m n))) /
                bergmanKernel m n interior_z interior_z) (𝓝[Ω] z) (𝓝 0)) ∧
          ¬IsCompactOperator T := by
  sorry

end Balay2022L
