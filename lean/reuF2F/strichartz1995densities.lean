import Mathlib

/-!
# Densities of Self-Similar Measures on the Line

Authors: Robert S. Strichartz, Arthur Taylor, and Tong Zhang.
Origin: [NSF Research Experiences for Undergraduates Program](https://www.maths.tcd.ie/EMIS/journals/EM/restricted/4/4.2/strich.ps).
Reference: R. S. Strichartz, A. Taylor, and T. Zhang, *Densities of Self-Similar Measures on the
Line*, Experiment. Math. **4** (1995), no. 2, 101-128.
-/

noncomputable section

namespace Strichartz1995Densities

open MeasureTheory
open scoped NNReal

/-- **Unnumbered conjecture** (following Problem 3.3, p. 111). Under Hypotheses 3.1, positive
Lipschitz projective weights determine at most one probability eigensolution of (3.3).

Interval weights cover the source's attractor-weight convention by positive Lipschitz extension;
the maps need only have uniformly shrinking composition mesh, and `c` is the source's scaling
constant `λ`. -/
theorem lipschitz_uniqueness
    {m : ℕ} (hm : 2 ≤ m)
    (S : Fin m → C(unitInterval, unitInterval))
    (hinj : ∀ j, Function.Injective (S j))
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint
        (interior (Set.range (fun x : unitInterval ↦ ((S i x : unitInterval) : ℝ))))
        (interior (Set.range (fun x : unitInterval ↦ ((S j x : unitInterval) : ℝ)))))
    (hmesh : ∀ ε > (0 : ℝ), ∃ N : ℕ,
      ∀ n ≥ N, ∀ w : Fin n → Fin m,
        ∀ x y : unitInterval,
          dist ((List.ofFn w).foldr (fun j f ↦ (S j) ∘ f) id x)
            ((List.ofFn w).foldr (fun j f ↦ (S j) ∘ f) id y) < ε)
    (q : Fin m → unitInterval → ℝ)
    (hq : ∀ j x, 0 < q j x)
    (hlip : ∀ j, ∃ L : ℝ≥0, LipschitzWith L (q j))
    (μ ν : ProbabilityMeasure unitInterval)
    (c η : ℝ) (hc : 0 < c) (hη : 0 < η)
    (hμ : ENNReal.ofReal c • (μ : Measure unitInterval) =
      ∑ j,
        ((μ : Measure unitInterval).withDensity (fun x ↦ ENNReal.ofReal (q j x))).map
          (S j))
    (hν : ENNReal.ofReal η • (ν : Measure unitInterval) =
      ∑ j,
        ((ν : Measure unitInterval).withDensity (fun x ↦ ENNReal.ofReal (q j x))).map
          (S j)) :
    μ = ν := by
  sorry

end Strichartz1995Densities
