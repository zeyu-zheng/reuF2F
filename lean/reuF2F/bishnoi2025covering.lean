import Mathlib

/-!
# Covering half-grids with lines and planes

Authors: Anurag Bishnoi and Shantanu Nene.
Origin: [Polymath Jr. 2023](https://geometrynyc.wixsite.com/polymathreu/results2023).
Reference: A. Bishnoi and S. Nene, *Covering half-grids with lines and planes*,
arXiv:2501.11156v3.
-/

noncomputable section

namespace Bishnoi2025Covering

open Finset

/-- A conical grid of order `n`: `n - i` points on the `i`th of `n` strictly increasing
horizontal levels, and no other points (Definition 1). -/
def IsConicalGrid (n : ℕ) (G : Finset (ℝ × ℝ)) : Prop :=
  0 < n ∧ ∃ a : Fin n → ℝ, StrictMono a ∧
    (∀ p ∈ G, ∃ i, p.2 = a i) ∧
    ∀ i : Fin n, #{p ∈ G | p.2 = a i} = n - i.val

open scoped Classical in
/-- **Conjecture 1** (p. 7). A single absolute positive constant `C` gives the lower bound
`2 * n * k / 3 - C * k` for every multiplicity cover of every conical grid. -/
theorem conjecture_1 :
    ∃ C > (0 : ℝ),
      ∀ (n k : ℕ) (G : Finset (ℝ × ℝ)), IsConicalGrid n G → 0 < k →
        ∀ L : Multiset (AffineSubspace ℝ (ℝ × ℝ)),
          (∀ l ∈ L, Module.finrank ℝ l.direction = 1) →
          (∀ p ∈ G, k ≤ (L.filter fun l ↦ p ∈ l).card) →
          (2 : ℝ) * n * k / 3 - C * k ≤ (L.card : ℝ) := by
  sorry

end Bishnoi2025Covering
