import Mathlib

/-!
# Two-type annihilating systems on the complete and star graph

Authors: Irina Cristali, Yufeng Jiang, Matthew Junge, Remy Kassem,
David Sivakoff, and Grayson York.
Origin: [Duke DOmath 2018](https://agraysonyork.com/research.html).
Reference: I. Cristali, Y. Jiang, M. Junge, R. Kassem, D. Sivakoff, and G. York, *Two-type
annihilating systems on the complete and star graph*, Stochastic Process. Appl. **139** (2021),
321--342.
-/

noncomputable section

namespace Cristali2021Two

open Filter
open scoped ENNReal NNReal Topology

/-- **Unnumbered conjecture** (Section 1.3). For every sufficiently large fixed blue-selection
probability `p < 1`, the expected extinction time on the star with `2 * n` initially occupied
leaves is asymptotic to `4 * log (1 / (1 - p)) * n`.

The limit is in `n` with `p` fixed, not an iterated limit or the always-blue-core heuristic;
selection is uniform among particles with multiplicity, the expectation is the extended
nonnegative survival-tail sum, and the initial leaves carry a canonical balanced coloring. -/
theorem section_1_3_star_asymptotic :
    ∃ p₀ ≥ (1 / 2 : ℝ≥0), p₀ < 1 ∧
      ∀ p : ℝ≥0, p₀ < p → (hp : p < 1) →
        Tendsto
          (fun n : ℕ ↦
            let V := Option (Fin (2 * n))
            let State := Multiset V × Multiset V
            let initial : State :=
              ((Finset.univ : Finset (Fin n)).val.map
                  (fun i ↦ some ⟨i.val, by omega⟩),
                (Finset.univ : Finset (Fin n)).val.map
                  (fun i ↦ some ⟨n + i.val, by omega⟩))
            let step : State → PMF State := fun s ↦
              if s.1 = 0 ∧ s.2 = 0 then PMF.pure s else
                (PMF.ofFintype (fun blue : Bool ↦
                    cond blue (p : ℝ≥0∞) (1 - (p : ℝ≥0∞)))
                  (by simp [show (p : ℝ≥0∞) ≤ 1 by exact_mod_cast hp.le])).bind
                  (fun blue ↦
                    if h : (if blue then s.1 else s.2) = 0 then PMF.pure s else
                      (PMF.ofMultiset (if blue then s.1 else s.2) h).bind (fun x ↦
                        if hN : ((SimpleGraph.starGraph (none : V)).neighborFinset x).Nonempty then
                          (PMF.uniformOfFinset
                              ((SimpleGraph.starGraph (none : V)).neighborFinset x) hN).map
                            (fun y ↦
                              if blue then
                                if y ∈ s.2 then (s.1.erase x, s.2.erase y)
                                else (y ::ₘ s.1.erase x, s.2)
                              else
                                if y ∈ s.1 then (s.1.erase y, s.2.erase x)
                                else (s.1, y ::ₘ s.2.erase x))
                        else PMF.pure s))
            (∑' t : ℕ,
                (((fun ν : PMF State ↦ ν.bind step)^[t]) (PMF.pure initial)).toOuterMeasure
                  {s | s.1 ≠ 0 ∨ s.2 ≠ 0}) / (n : ℝ≥0∞))
          atTop (𝓝 (ENNReal.ofReal (4 * Real.log (1 / (1 - (p : ℝ)))))) := by
  sorry

end Cristali2021Two
