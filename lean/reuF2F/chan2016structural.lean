import Mathlib

/-!
# On structural decompositions of finite frames

Authors: Alice Z.-Y. Chan, Martin S. Copenhaver, Sivaram K. Narayan, Logan Stokols,
and Allison Theobold.
Origin: [Central Michigan University REU 2013](https://arxiv.org/abs/1411.6138).
Reference: A. Z.-Y. Chan, M. S. Copenhaver, S. K. Narayan, L. Stokols, and A. Theobold, *On
structural decompositions of finite frames*, Adv. Comput. Math. **42** (2016), 721-756;
doi:10.1007/s10444-015-9440-1.
-/

namespace Chan2016Structural

open scoped RealInnerProductSpace

open scoped Classical in
/-- The factor poset: the indexed tight subframes, together with the empty set (Definition 7). -/
noncomputable def factorPoset {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n)) :
    Finset (Finset (Fin k)) :=
  {s | s = ∅ ∨
    ∃ A > (0 : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i ∈ s, ⟪x, F i⟫ ^ 2 = A * ‖x‖ ^ 2}

open scoped Classical in
/-- The scalability poset: the subframes admitting a nonnegative Parseval scaling, with the empty
set included by convention (Definitions 13 and 16). -/
noncomputable def scalabilityPoset {n k : ℕ} (F : Fin k → EuclideanSpace ℝ (Fin n)) :
    Finset (Finset (Fin k)) :=
  {s | s = ∅ ∨
    ∃ w : Fin k → ℝ, (∀ i ∈ s, 0 ≤ w i) ∧
      ∀ x : EuclideanSpace ℝ (Fin n), ∑ i ∈ s, w i * ⟪x, F i⟫ ^ 2 = ‖x‖ ^ 2}

/-- **Conjecture 3**. Unit-norm frames with the same scalability poset admit a
strict scaling reproducing the factor poset of either frame that is tight. -/
theorem conjecture_3 {n k : ℕ} (F G : Fin k → EuclideanSpace ℝ (Fin n))
    (hF : Submodule.span ℝ (Set.range F) = ⊤)
    (hFunit : ∀ i, ‖F i‖ = 1) (hGunit : ∀ i, ‖G i‖ = 1)
    (hG : ∃ A > (0 : ℝ), ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ i, ⟪x, G i⟫ ^ 2 = A * ‖x‖ ^ 2)
    (hsame : scalabilityPoset F = scalabilityPoset G) :
    ∃ w : Fin k → ℝ, (∀ i, 0 < w i) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ∑ i, w i * ⟪x, F i⟫ ^ 2 = ‖x‖ ^ 2) ∧
      factorPoset (fun i ↦ √(w i) • F i) = factorPoset G := by
  sorry

end Chan2016Structural
