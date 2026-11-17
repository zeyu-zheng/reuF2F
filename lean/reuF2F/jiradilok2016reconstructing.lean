import Mathlib

/-!
# Reconstructing Partitions from their Multisets of k-Minors

Author: Pakawut Jiradilok.
Origin: [University of Minnesota Duluth REU 2016](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: P. Jiradilok, *Reconstructing partitions from their multisets of k-minors*,
arXiv:1610.05354v1.
-/

namespace Jiradilok2016Reconstructing

open Finset

open scoped Classical in
/-- The number `N(λ / μ)` of standard skew tableaux, zero when `μ ⊄ λ` (Section 2).
Entries are reindexed from `1, …, k` to `Fin k`. -/
noncomputable def skewTableauCount (lam μ : YoungDiagram) : ℕ :=
  if μ ≤ lam then
    {T : Equiv {b // b ∈ lam.cells \ μ.cells}
        (Fin #(lam.cells \ μ.cells)) |
      (∀ b c, b.val.1 = c.val.1 → b.val.2 < c.val.2 → T b < T c) ∧
      (∀ b c, b.val.2 = c.val.2 → b.val.1 < c.val.1 → T b < T c)}.ncard
  else 0

open scoped Classical in
/-- The largest `k ≤ n` for which the multiset of `k`-minors, with skew-tableau multiplicities,
determines every partition of `n`, `G(n)` (Section 2). -/
noncomputable def G (n : ℕ) : ℕ :=
  ({k ∈ Finset.range (n + 1) |
    Function.Injective (fun lam : {lam : YoungDiagram // lam.card = n} ↦
      fun μ : {μ : YoungDiagram // μ.card = n - k} ↦
        skewTableauCount lam.val μ.val)}).sup id

/-- **Conjecture 7.1** (p. 27). The reconstruction deficit `n - G(n)` tends to infinity. -/
theorem conjecture_7_1 :
    Filter.Tendsto (fun n : ℕ ↦ n - G n) Filter.atTop Filter.atTop := by
  sorry

end Jiradilok2016Reconstructing
