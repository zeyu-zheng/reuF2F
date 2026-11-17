import Mathlib

/-!
# Sub-Fibonacci behavior in numerical semigroup enumeration

Author: Daniel G. Zhu.
Origin: [University of Minnesota Duluth REU 2020](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: D. G. Zhu, *Sub-Fibonacci behavior in numerical semigroup enumeration*,
arXiv:2202.05755v3, 2023.
-/

noncomputable section

namespace Zhu2023Sub

open scoped Topology

/-- Kunz words: positive integer words satisfying both one-indexed Kunz inequalities
(Definition 3.2). -/
def IsKunz (w : List ℕ) : Prop :=
  (∀ a ∈ w, 0 < a) ∧
  ∀ i j : ℕ, 1 ≤ i → i ≤ w.length → 1 ≤ j → j ≤ w.length →
    (i + j ≤ w.length →
      w.getD (i + j - 1) 0 ≤ w.getD (i - 1) 0 + w.getD (j - 1) 0) ∧
    (w.length + 1 < i + j →
      w.getD (i + j - w.length - 2) 0 ≤ w.getD (i - 1) 0 + w.getD (j - 1) 0 + 1)

/-- **Conjecture 7.3(a)-(c)**. Deep numerical semigroups and stressed Kunz words have the
proposed exponential rate, successive-count ratio, and polynomial correction. -/
theorem conjecture_7_3 (ρ : ℝ) (hρ : 0 < ρ)
    (hroot : ρ ^ 6 - ρ ^ 3 - 2 * ρ ^ 2 - 2 * ρ - 1 = 0) :
    let counts : Bool → ℕ → ℕ := fun stressed g ↦
      {w : List ℕ | IsKunz w ∧ w.sum = g ∧
        if stressed then (∀ a ∈ w, a ≤ 3) ∧ w.getLast? = some 3
        else ∃ a ∈ w, 4 ≤ a}.ncard
    (∀ stressed : Bool, Filter.Tendsto
      (fun g : ℕ ↦ (counts stressed g : ℝ) ^ (1 / (g : ℝ)))
      Filter.atTop (𝓝 ρ)) ∧
    (∀ stressed : Bool, Filter.Tendsto
      (fun g : ℕ ↦ (counts stressed (g + 1) : ℝ) / (counts stressed g : ℝ))
      Filter.atTop (𝓝 ρ)) ∧
    (∀ stressed : Bool, ∃ α : ℝ, Filter.Tendsto
      (fun g : ℕ ↦ (Real.log (counts stressed g) - (g : ℝ) * Real.log ρ) /
        Real.log g) Filter.atTop (𝓝 α)) := by
  sorry

end Zhu2023Sub
