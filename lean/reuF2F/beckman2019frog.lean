import Mathlib

/-!
# The frog model on trees with drift

Authors: Erin Beckman, Natalie Frank, Yufeng Jiang, Matthew Junge, and Si Tang.
Origin: [Duke DOmath 2018](https://math.duke.edu/domath/2018).
Reference: E. Beckman, N. Frank, Y. Jiang, M. Junge, and S. Tang, *The frog model on trees with
drift*, Electron. Commun. Probab. **24** (2019); doi:10.1214/19-ECP235; arXiv:1808.03283v1.
-/

noncomputable section

namespace Beckman2019Frog

open MeasureTheory ProbabilityTheory
open scoped Topology

/-- Vertices of the rooted `d`-ary tree as words with zero-based child labels (Section 5). -/
abbrev Vertex (d : ℕ) := List (Fin d)

/-- The one-per-site frog model: active frog labels and positions after each simultaneous step
(Section 1). Instructions are indexed by time and frog label, with `true` selecting the parent
except at the root; woken frogs start moving at the next step. -/
def frogProcess {d : ℕ} (instructions : ℕ × Vertex d → Bool × Fin d) :
    ℕ → Finset (Vertex d) × (Vertex d → Vertex d)
  | 0 => ({[]}, id)
  | t + 1 =>
      let state := frogProcess instructions t
      let position := fun v ↦
        if v ∈ state.1 then
          let x := state.2 v
          if x ≠ [] ∧ (instructions (t, v)).1 = true then x.dropLast
          else x ++ [(instructions (t, v)).2]
        else state.2 v
      (state.1 ∪ state.1.image position, position)

/-- The critical drift: the infimum of recurrent drifts for the one-per-site frog model
(Section 1, p. 2). The recurrence set need not be an interval or contain its infimum. -/
def criticalDrift (d : ℕ) [NeZero d] : ℝ :=
  sInf {r : ℝ | ∃ p : unitInterval, r = (p : ℝ) ∧
    ∀ᵐ instructions ∂Measure.infinitePi (fun _ : ℕ × Vertex d ↦
      (bernoulliMeasure true false p).prod (PMF.uniformOfFintype (Fin d)).toMeasure),
      Set.Infinite {t : ℕ | ∃ v ∈ (frogProcess instructions t).1,
        (frogProcess instructions t).2 v = []}}

/-- **Open problem** (Section 1, p. 2). The critical drift weakly decreases as the
degree increases, and hence has a real limit.

No specific limit or strict decrease is asserted. The root always moves to a child, even at
drift one. -/
theorem critical_drift_monotonicity :
    (∀ d : ℕ, ∀ hd : 2 ≤ d,
      letI : NeZero d := ⟨by omega⟩
      criticalDrift (d + 1) ≤ criticalDrift d) ∧
    ∃ L : ℝ, Filter.Tendsto (fun n : ℕ ↦ criticalDrift (n + 2))
      Filter.atTop (𝓝 L) := by
  sorry

end Beckman2019Frog
