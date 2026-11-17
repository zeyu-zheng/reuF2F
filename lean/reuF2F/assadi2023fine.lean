import Mathlib

/-!
# Fine-Grained Buy-Many Mechanisms Are Not Much Better Than Bundling

Authors: Sepehr Assadi, Vikram Kher, George Li, and Ariel Schvartzman.
Origin: [DIMACS REU 2022](https://arxiv.org/pdf/2205.14312v2#page=1).
Reference: S. Assadi, V. Kher, G. Li, and A. Schvartzman, *Fine-grained buy-many mechanisms are
not much better than bundling*, in Proc. EC (2023); doi:10.1145/3580507.3597662;
arXiv:2205.14312v2.
-/

noncomputable section

namespace Assadi2023Fine

open MeasureTheory
open scoped NNReal ENNReal

/-- Finite-valued monotone valuations of two items, normalized at no purchase (Section 2). -/
abbrev Valuation :=
  {v : Finset (Fin 2) → ℝ≥0 // v ∅ = 0 ∧ Monotone v}

/-- An allocation: an independent probability for each item (Section 2). -/
abbrev Allocation := Fin 2 → Set.Icc (0 : ℝ) 1

/-- The expected value of a product-Bernoulli allocation (Section 2). -/
def allocationValue (v : Valuation) (q : Allocation) : ℝ :=
  ∑ S : Finset (Fin 2), (v.val S : ℝ) *
    (∏ j ∈ S, (q j : ℝ)) * (∏ j ∈ Finset.univ \ S, (1 - (q j : ℝ)))

/-- The allocation `Lot` of a union of independently drawn, nonadaptively chosen tickets
(Section 2). -/
def lottery {m : ℕ} (q : Fin m → Allocation) : Allocation :=
  fun j ↦ ⟨1 - ∏ a, (1 - (q a j : ℝ)), by
    constructor
    · exact sub_nonneg.mpr (Finset.prod_le_one₀
        (fun a _ ↦ sub_nonneg.mpr (q a j).property.2)
        (fun a _ ↦ sub_le_self 1 (q a j).property.1))
    · exact sub_le_self 1 (Finset.prod_nonneg
        (fun a _ ↦ sub_nonneg.mpr (q a j).property.2))⟩

/-- A direct mechanism: a price and allocation for each valuation in the support (Section 2). -/
structure Mechanism (D : ProbabilityMeasure Valuation) where
  /-- The price charged for each valuation in the support. -/
  price : (D : Measure Valuation).support → ℝ≥0
  /-- The allocation offered for each valuation in the support. -/
  allocation : (D : Measure Valuation).support → Allocation
  measurable_price : Measurable price
  measurable_allocation : Measurable allocation

/-- Pointwise buy-`k` incentive compatibility, including empty purchases (Section 2). -/
def Mechanism.BuyKIC {D : ProbabilityMeasure Valuation} (M : Mechanism D) (k : ℕ) : Prop :=
  ∀ v : (D : Measure Valuation).support, ∀ m : ℕ, m ≤ k →
    ∀ reports : Fin m → (D : Measure Valuation).support,
      allocationValue v.val (lottery (fun a ↦ M.allocation (reports a))) -
        ∑ a, (M.price (reports a) : ℝ) ≤
      allocationValue v.val (M.allocation v) - (M.price v : ℝ)

/-- **Conjecture 1**. Some two-item distribution strictly separates every pair of consecutive
optimal buy-`k` revenues.

Optimal revenues are greatest achievable values. Normalization, Borel measurable support-wise
mechanisms and designated weak-IC tie selection make the source's informal conventions explicit;
valuations need not be additive or finitely supported. -/
theorem conjecture_1 :
    ∃ D : ProbabilityMeasure Valuation, ∃ r : ℕ → ℝ≥0∞, ∀ k ≥ 1,
      IsGreatest
        {z : ℝ≥0∞ | ∃ M : Mechanism D, M.BuyKIC k ∧
          z = ∫⁻ v, (M.price v : ℝ≥0∞)
            ∂((D : Measure Valuation).comap
              (Subtype.val : (D : Measure Valuation).support → Valuation))}
        (r k) ∧ r (k + 1) < r k := by
  sorry

end Assadi2023Fine
