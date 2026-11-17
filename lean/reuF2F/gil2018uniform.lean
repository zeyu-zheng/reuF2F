import Mathlib

/-!
# Uniform Generation of w-free Strings and H-free Subgraphs with Partial Rejection Sampling

Authors: Juan Gil and Joshua Amaniampong.
Origin: [MIT SPUR 2018](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: J. Gil and J. Amaniampong, *Uniform Generation of w-free Strings and H-free
Subgraphs with Partial Rejection Sampling*, MIT SPUR final paper, 2018.
-/

noncomputable section

namespace Gil2018Uniform

open Filter
open scoped ENNReal
open Finset

/-- The bad events: all starting positions of an occurrence of `w` (Section 2.1). Positions are
zero-based, and every complete window, including the last, is tested. -/
def badEvents (w x : List Bool) : Finset ℕ :=
  {i ∈ Finset.range (x.length + 1 - w.length) | (x.drop i).take w.length = w}

/-- The set `var(R)` of positions belonging to the selected word events (Sections 2-3). -/
def eventVariables (k : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.biUnion fun i ↦ Finset.Ico i (i + k)

/-- The resampling set (Algorithm 2). It uses the simultaneous boundary update of the authors'
SPUR implementation, iterated once per window since each nonterminal pass marks a new event. -/
def resamplingSet (w x : List Bool) : Finset ℕ :=
  let positions := Finset.range (x.length + 1 - w.length)
  let pass := fun RN : Finset ℕ × Finset ℕ ↦
    let boundary := {i ∈ positions |
      i ∉ RN.1 ∧ i ∉ RN.2 ∧
        ∃ j ∈ RN.1, ¬Disjoint (Finset.Ico i (i + w.length))
          (Finset.Ico j (j + w.length))}
    let unblocked := {i ∈ boundary |
      ∀ j ∈ Finset.Ico i (i + w.length) ∩ eventVariables w.length RN.1,
        x[j]? = w[j - i]?}
    (RN.1 ∪ unblocked, RN.2 ∪ (boundary \ unblocked))
  ((pass^[#positions]) (badEvents w x, ∅)).1

/-- The successive assignments, starting from the initial independent sample (Algorithm 3). Each
draw replaces exactly the selected variables, so a terminal assignment remains fixed. -/
def assignments (w : List Bool) {n : ℕ} (initial : Fin n → Bool)
    (draws : List (Fin n → Bool)) : List (Fin n → Bool) :=
  draws.scanl (fun x draw ↦
    let R := eventVariables w.length (resamplingSet w (List.ofFn x))
    fun i ↦ if i.val ∈ R then draw i else x i) initial

/-- **Unnumbered conjecture** (Section 6.1). For binary words, PRS takes quadratic expected
rounds for `01` and `10`, and logarithmic expected rounds for `00`, `11` and all words of length
at least three.

The tail sum uses independent fair-bit tables, including the initial sample, and the
simultaneous expansion convention of the authors' linked program. -/
theorem conjecture_6_1 (w : List Bool) :
    let E : ℕ → ℝ≥0∞ := fun n ↦ ∑' t : ℕ,
      (#{tape : Fin (t + 1) → Fin n → Bool |
        (badEvents w (List.ofFn
          ((assignments w (tape 0) (List.ofFn tape).tail).getLastD (tape 0)))).Nonempty} :
            ℝ≥0∞) /
          2 ^ (n * (t + 1))
    ((w = [false, true] ∨ w = [true, false]) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (c * (n : ℝ) ^ 2) ≤ E n ∧
          E n ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2)) ∧
    ((3 ≤ w.length ∨ w = [false, false] ∨ w = [true, true]) →
      ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        E n ≤ ENNReal.ofReal (C * Real.log (n : ℝ))) := by
  sorry

end Gil2018Uniform
