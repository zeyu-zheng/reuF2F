import Mathlib

/-!
# Hat-Guessing on Graphs

Authors: Zhuoer Gu, Yuzu Ido, and Benjamin Przybocki.
Origin: [Stanford SURIM](https://surim.stanford.edu/publications/combinatorics/hat-guessing-graphs).
Reference: Z. Gu, Y. Ido, and B. Przybocki, *Hat-Guessing on Graphs*, Stanford SURIM report, 2020.
-/

noncomputable section

namespace Gu2020Hat

open SimpleGraph Finset

/-- A guessing strategy for vertex `v` in the `q`-color hat-guessing game on `G`. -/
structure HatStrategy {V : Type*} (G : SimpleGraph V) (q : ℕ) (v : V) where
  /-- The guess for `v`'s hat color, given a hat assignment. -/
  guess : (V → Fin q) → Fin q
  /-- The guess depends only on the colors of `v`'s neighbors. -/
  locality : ∀ h₁ h₂ : V → Fin q,
    (∀ w, G.Adj v w → h₁ w = h₂ w) → guess h₁ = guess h₂

/-- The graph `G` is hat-guessable with `q` colors: a winning strategy profile exists. The
conjunct `0 < q` records the source convention that the color set is nonempty. -/
def HatGuessable {V : Type*} (G : SimpleGraph V) (q : ℕ) : Prop :=
  0 < q ∧ ∃ s : (v : V) → HatStrategy G q v,
    ∀ h : V → Fin q, ∃ v, (s v).guess h = h v

/-- **Conjecture 3.8**. For `n ≥ 3`, the hat-guessing number satisfies `HG(K_{n,n}) ≤ n`.

The best previously known bound is `HG(K_{n,n}) ≤ n + 1` (Gadouleau–Georgiou). -/
theorem conjecture_knn_upper_bound (n : ℕ) (hn : 3 ≤ n) (r : ℕ) (hr : 0 < r)
    (hG : HatGuessable (completeBipartiteGraph (Fin n) (Fin n) : SimpleGraph (Fin n ⊕ Fin n)) r) :
    r ≤ n := by
  sorry

end Gu2020Hat
