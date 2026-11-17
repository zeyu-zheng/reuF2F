import Mathlib

/-!
# On rationally ergodic and rationally weakly mixing rank-one transformations

Authors: Irving Dai, Xavier Garcia, Tudor Padurariu, and Cesar E. Silva.
Origin: Williams College SMALL REU 2012.
Reference: I. Dai, X. Garcia, T. Padurariu, and C. E. Silva, *On rationally ergodic and rationally
weakly mixing rank-one transformations*, Ergodic Theory Dynam. Systems **35** (2015), no. 4,
1141--1164; arXiv:1208.3161v2.
-/

noncomputable section

namespace Dai2015Rationally

open MeasureTheory Set Filter
open scoped ENNReal

/-- The common width of the levels at stage `n`, starting with unit width and cutting into
`cuts k` equal pieces at each preceding stage (Section 1.3). -/
def columnWidth (cuts : ℕ → ℕ) (n : ℕ) : ℝ :=
  (∏ k ∈ Finset.range n, (cuts k : ℝ))⁻¹

/-- The ordered left endpoints of the interval levels of a column. Old levels are cut left to
right, spacers follow the old occupied interval, and list order is tower order. -/
def columnStarts (cuts : ℕ → ℕ) (spacers : ℕ → ℕ → ℕ) : ℕ → List ℝ
  | 0 => [0]
  | n + 1 =>
    let old := columnStarts cuts spacers n
    let w := columnWidth cuts (n + 1)
    let endOfOld := (old.length : ℝ) * columnWidth cuts n
    (List.range (cuts n)).flatMap fun (k : ℕ) ↦
      old.map (fun a ↦ a + (k : ℝ) * w) ++
        (List.range (spacers n k)).map (fun (j : ℕ) ↦
          endOfOld + (((∑ u ∈ Finset.range k, spacers n u) + j : ℕ) : ℝ) * w)

/-- **Unnumbered conjecture** (Introduction, p. 3). The almost-steep construction of Section 4
and Theorem 4.4 is doubly ergodic for all positive-measure measurable sets, not just levels.

The cutting and spacer data are arbitrary summable data, and the transformation is specified
modulo null endpoints by its upward column translations. -/
theorem almost_steep_doubly_ergodic
    (cuts : ℕ → ℕ) (spacers : ℕ → ℕ → ℕ)
    (hcuts : ∀ n, 3 ≤ cuts n)
    (hfirst : ∀ n, spacers n 0 = 0)
    (hsecond : ∀ n, spacers n 1 = 1)
    (hsteep : ∀ n i, 2 ≤ i → i < cuts n →
      4 * (∑ k ∈ Finset.range i, ((columnStarts cuts spacers n).length + spacers n k)) ≤
        ∑ k ∈ Finset.range (i + 1), ((columnStarts cuts spacers n).length + spacers n k))
    (hsummable : Summable (fun n ↦ (cuts n : ℝ)⁻¹))
    (T : ℝ ≃ᵐ ℝ)
    (hergodic : Ergodic T (volume.restrict (Ici (0 : ℝ))))
    (hconservative : Conservative T (volume.restrict (Ici (0 : ℝ))))
    (hcolumns : ∀ n j, j + 1 < (columnStarts cuts spacers n).length →
      ∀ᵐ x ∂(volume.restrict (Ici (0 : ℝ))),
        x ∈ Ioo ((columnStarts cuts spacers n).getD j 0)
          ((columnStarts cuts spacers n).getD j 0 + columnWidth cuts n) →
        T x = x - (columnStarts cuts spacers n).getD j 0 +
          (columnStarts cuts spacers n).getD (j + 1) 0)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA₀ : 0 < (volume.restrict (Ici (0 : ℝ))) A)
    (hB₀ : 0 < (volume.restrict (Ici (0 : ℝ))) B) :
    ∃ m > 0,
      0 < (volume.restrict (Ici (0 : ℝ))) (A ∩ (T^[m]) ⁻¹' A) ∧
      0 < (volume.restrict (Ici (0 : ℝ))) (A ∩ (T^[m]) ⁻¹' B) := by
  sorry

end Dai2015Rationally
