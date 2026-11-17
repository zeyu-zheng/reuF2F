import Mathlib

/-!
# Circular Trace Reconstruction

Authors: Shyam Narayanan and Michael Ren.
Origin: [University of Minnesota Duluth REU
2020](https://sites.google.com/view/gallian-reu/additional-information/program-bibliography).
Reference: S. Narayanan and M. Ren, *Circular Trace Reconstruction*, in ITCS 2021, LIPIcs
**185** (2021), 18:1-18:18; arXiv:2009.01346v2.
-/

noncomputable section

namespace Narayanan2020Circular

open Filter
open scoped Topology

/-- **Open problem 3** (Section 6, arXiv v2 p. 16). Average-case circular trace reconstruction
succeeds with probability tending to one from a subpolynomial number of traces.

The uniformly random word is uniformly rotated, and each trace rotates it uniformly before
independent deletions with probability `q`; the rule is a deterministic function of the trace
tuple, and success means recovering the word up to rotation. -/
theorem open_problem_3 (q : ℝ) (hq : 0 < q) (hq₁ : q < 1) :
    ∃ (T : ℕ → ℕ)
      (D : (n : ℕ) → List.Vector {trace : List Bool // trace.length ≤ n + 1} (T n) →
        Fin (n + 1) → Bool),
      (∀ n, 0 < T n) ∧
      (∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, (T n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ ε) ∧
      Tendsto
        (fun n ↦
          let experiment : PMF ((Fin (n + 1) → Bool) × (Fin (n + 1) → Bool)) :=
            (PMF.uniformOfFintype (Fin (n + 1) → Bool)).bind fun bits ↦
              (PMF.uniformOfFintype (Fin (n + 1))).bind fun initialRotation ↦
                let x : Fin (n + 1) → Bool := fun i ↦ bits (finCycle initialRotation i)
                let traceLaw : PMF {trace : List Bool // trace.length ≤ n + 1} :=
                  (PMF.uniformOfFintype (Fin (n + 1))).bind fun rotation ↦
                    PMF.map (fun deleted : List.Vector Bool (n + 1) ↦
                      Subtype.mk
                        (((List.finRange (n + 1)).filter fun i ↦ !deleted.get i).map
                          fun i ↦ x (finCycle rotation i))
                        (by
                          simp only [List.length_map]
                          exact (List.length_filter_le _ _).trans_eq List.length_finRange))
                      (List.Vector.mOfFn fun _ : Fin (n + 1) ↦
                        (ProbabilityTheory.bernoulliMeasure true false
                          ⟨q, hq.le, hq₁.le⟩).toPMF)
                PMF.map (fun traces ↦ (x, D n traces))
                  (List.Vector.mOfFn fun _ : Fin (T n) ↦ traceLaw)
          (experiment.toOuterMeasure
            {result | List.IsRotated (List.ofFn result.2) (List.ofFn result.1)}).toReal)
        atTop (𝓝 1) := by
  sorry

end Narayanan2020Circular
