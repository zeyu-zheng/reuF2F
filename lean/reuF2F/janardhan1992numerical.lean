import Mathlib

/-!
# Numerical Experiments in Fourier Asymptotics of Cantor Measures and Wavelets

Authors: Prem Janardhan, David Rosenblum, and Robert S. Strichartz.
Origin: [NSF Research Experiences for Undergraduates Program](https://emis.muni.cz/journals/EM/restricted/1/1.4/janardhan.ps.gz).
Reference: P. Janardhan, D. Rosenblum, and R. S. Strichartz, *Numerical experiments in Fourier
asymptotics of Cantor measures and wavelets*, Experiment. Math. **1** (1992), no. 4, 249-273;
doi:10.1080/10586458.1992.10504561.
-/

namespace Janardhan1992Numerical

open scoped Topology

/-- **Conjecture 5.1** (p. 266). Every positive real moment of a normalized continuous solution
of the two-scale recursion has a finite logarithmic integral-growth exponent.

The printed `x → 0` is read as `x → ∞`, as (1.9), (5.1) and (5.3)-(5.4) indicate; each
coefficient has its own positive period, with no common-period restriction. -/
theorem conjecture_5_1
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 1 < ρ₁) (hρ₂ : 1 < ρ₂)
    (f₁ f₂ : ℝ → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hpos₁ : ∀ t, 0 < f₁ t) (hpos₂ : ∀ t, 0 < f₂ t)
    (hperiod₁ : ∃ T > (0 : ℝ), Function.Periodic f₁ T)
    (hperiod₂ : ∃ T > (0 : ℝ), Function.Periodic f₂ T)
    (hnormalize : f₁ 0 + f₂ 0 = 1)
    (F : ℝ → ℝ) (hF : Continuous F) (hF₀ : F 0 = 1)
    (hrecurrence : ∀ t : ℝ,
      F t = f₁ (t / ρ₁) * F (t / ρ₁) + f₂ (t / ρ₂) * F (t / ρ₂))
    (q : ℝ) (hq : 0 < q) :
    ∃ b : ℝ,
      Filter.Tendsto
        (fun x : ℝ ↦ Real.log (∫ t in (0 : ℝ)..x, |F t| ^ q) / Real.log x)
        Filter.atTop (𝓝 b) := by
  sorry

end Janardhan1992Numerical
