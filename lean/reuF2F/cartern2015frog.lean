import Mathlib

/-!
# Frog model wakeup time on the complete graph

Authors: Nikki Cartern, Brittany Dygert, Matthew Junge, Stephen Lacina,
Collin Litterell, Austin Stromme, and Andrew You.
Origin: [University of Washington REU 2015](https://sites.math.washington.edu/~reu/papers/2015/).
Reference: N. Cartern, B. Dygert, M. Junge, S. Lacina, C. Litterell, A. Stromme, and A. You,
*Frog model wakeup time on the complete graph*, arXiv:1510.05995.
-/

open Filter MeasureTheory
open scoped Topology ENNReal

namespace Cartern2015Frog

/-- The awake sets and frog positions over time, from the initial state (Section 2.1). Only awake
frogs move in a step, and frogs at their destinations wake afterwards. -/
noncomputable def frogStates {n : ℕ} (root : Fin n)
    (moves : List (Fin n → Fin n)) : List (Finset (Fin n) × (Fin n → Fin n)) :=
  moves.scanl (fun s move ↦
    let position := fun v ↦ if v ∈ s.1 then move v else s.2 v
    (s.1 ∪ s.1.image position, position)) ({root}, id)

open scoped Classical in
/-- **Further Question (ii)** (Section 1.2). For each fixed positive edge density, the frog model
on an Erdos-Renyi graph wakes every frog in logarithmic time with high probability. -/
theorem further_questions_ii (p : unitInterval) (hp : 0 < (p : ℝ)) :
    ∃ C > (0 : ℝ),
      Tendsto (fun n : ℕ ↦
        ∫⁻ G : SimpleGraph (Fin (n + 1)),
          ∑' moves : Fin ⌊C * Real.log (n + 1)⌋₊ → Fin (n + 1) → Fin (n + 1),
            if ((frogStates 0 (List.ofFn moves)).getLastD ({0}, id)).1 = Finset.univ then
              ∏ t : Fin ⌊C * Real.log (n + 1)⌋₊, ∏ v : Fin (n + 1),
                let s := (frogStates 0 (List.ofFn moves)).getD t.val ({0}, id)
                let jump := if v ∈ s.1 then
                  if h : (G.neighborFinset (s.2 v)).Nonempty then
                    PMF.uniformOfFinset (G.neighborFinset (s.2 v)) h
                  else PMF.pure (s.2 v)
                else PMF.pure (s.2 v)
                jump (moves t v)
            else 0
          ∂(SimpleGraph.binomialRandom (Fin (n + 1)) p))
        atTop (𝓝 1) := by
  sorry

end Cartern2015Frog
