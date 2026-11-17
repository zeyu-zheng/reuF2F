import Mathlib

/-!
# Effect of Transaction Tax on Optimal Portfolio Liquidation and Predatory Trading

Author: Enkhjargal Lkhagvajav.
Origin: [University of Michigan REU
2014](https://prod.lsa.umich.edu/content/dam/math-assets/math-document/reu-documents/Lkhagvajav%20REU%202014.pdf).
Reference: E. Lkhagvajav, *Effect of Transaction Tax on Optimal Portfolio Liquidation and
Predatory Trading*, University of Michigan REU report (August 1, 2014), 14 pp.
-/

noncomputable section

namespace Lkhagvajav2014Effect

open MeasureTheory

/-- Deterministic admissible strategies on the liquidation interval (Section 2.1). -/
def Admissible (x T : ℝ) (X : ℝ → ℝ) : Prop :=
  X 0 = x ∧ X T = 0 ∧ AbsolutelyContinuousOnInterval X 0 T ∧
    MemLp (deriv X) 2 (volume.restrict (Set.Icc 0 T)) ∧
      ∃ c ≥ (0 : ℝ), ∀ t ∈ Set.Icc 0 T, |X t| ≤ c

/-- **Unnumbered conjecture** (abstract and Introduction). With a smooth tax, every admissible
finite-agent market has a deterministic mean-variance Nash equilibrium.

The objective uses the deterministic form (15)-(16), with the printed path and index slips of
(14)-(15) corrected to the deviating path `Y`, opponents other than `i` and risk aversion
`alpha i`; nonnegative tax and positive horizon are contextual conventions, `n = 0` is the empty
market, and `c` is the source's `λ`. -/
theorem smooth_tax_equilibrium_exists
    {n : ℕ} (x α : Fin n → ℝ) (T S₀ σ γ c μ ε : ℝ)
    (b : ℝ → ℝ) (hT : 0 < T) (hα : ∀ i, 0 ≤ α i)
    (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hc : 0 < c)
    (hμ : 0 ≤ μ) (hε : 0 < ε) (hb : ContinuousOn b (Set.Icc 0 T)) :
    let utility := fun (X : Fin n → ℝ → ℝ) (i : Fin n) (Y : ℝ → ℝ) ↦
      x i * S₀ - γ / 2 * (x i) ^ 2 + μ * ε * T +
        ∫ t in (0 : ℝ)..T,
          Y t * (b t + γ * ∑ j ∈ Finset.univ.erase i, deriv (X j) t) -
            α i * σ ^ 2 / 2 * (Y t) ^ 2 -
            c * deriv Y t *
              ((∑ j ∈ Finset.univ.erase i, deriv (X j) t) + deriv Y t) -
            μ * √((deriv Y t) ^ 2 + ε ^ 2)
    ∃ X : Fin n → ℝ → ℝ,
      (∀ i, Admissible (x i) T (X i)) ∧
        ∀ (i : Fin n) (Y : ℝ → ℝ), Admissible (x i) T Y →
          utility X i Y ≤ utility X i (X i) := by
  sorry

end Lkhagvajav2014Effect
