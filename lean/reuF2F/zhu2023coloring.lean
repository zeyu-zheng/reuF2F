import Mathlib

/-!
# Coloring Bipartite Graphs with Semi-small List Size

Author: Daniel G. Zhu.
Origin: [University of Minnesota Duluth REU 2020](https://www.d.umn.edu/~jgallian/progbib.html).
Reference: D. G. Zhu, *Coloring bipartite graphs with semi-small list size*, Ann. Comb. **27**
(2023), 469-491; doi:10.1007/s00026-022-00633-z.
-/

noncomputable section

namespace Zhu2023Coloring

open scoped Topology
open Finset

/-- Asymmetric list choosability for the specified ordered vertex parts. -/
def Choosable {a b : ℕ} (G : SimpleGraph (Fin a ⊕ Fin b)) (kA kB : ℕ) : Prop :=
  ∀ L : (Fin a ⊕ Fin b) → Finset ℕ,
    (∀ v : Fin a, #(L (Sum.inl v)) = kA) →
    (∀ v : Fin b, #(L (Sum.inr v)) = kB) →
    ∃ c : G.Coloring ℕ, ∀ v, c v ∈ L v

/-- The invariant `xi`, with natural logarithm and partwise maximum degrees (Definition 2.7). -/
def xi (deltaA deltaB kA kB : ℕ) : ℝ :=
  (deltaB : ℝ) * Real.log (deltaA : ℝ) ^ (kA - 1) / (kB : ℝ) ^ kA

open scoped Classical in
/-- The infimum of `xi` over all non-choosable ordered bipartite graphs (Definition 6.1). -/
def xiG (kA : ℕ) : ℝ :=
  sInf {x : ℝ | ∃ (a b : ℕ) (G : SimpleGraph (Fin a ⊕ Fin b))
    (kB : ℕ), 0 < kB ∧ G ≤ completeBipartiteGraph (Fin a) (Fin b) ∧
    ¬Choosable G kA kB ∧
    x = xi (Finset.univ.sup (fun v : Fin a ↦ G.degree (Sum.inl v)))
      (Finset.univ.sup (fun v : Fin b ↦ G.degree (Sum.inr v))) kA kB}

/-- **Conjecture 1.11**. All optimal general-bipartite thresholds are positive, and their
logarithms divided by the first list size have a finite limit. -/
theorem conjecture_1_11 :
    (∀ kA > 0, 0 < xiG kA) ∧
    ∃ c : ℝ, Filter.Tendsto (fun kA : ℕ ↦ Real.log (xiG kA) / (kA : ℝ))
      Filter.atTop (𝓝 c) := by
  sorry

end Zhu2023Coloring
