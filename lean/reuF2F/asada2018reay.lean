import Mathlib

/-!
# On Reay's Relaxed Tverberg Conjecture and Generalizations of Conway's Thrackle Conjecture

Authors: Megumi Asada, Ryan Chen, Florian Frick, Frederick Huang, Maxwell Polevy,
David Stoner, Ling Hei Tsang, and Zoe Wellner.
Origin: [Cornell SPUR
2016](https://math.cornell.edu/history-reu-and-spur-programs-department-mathematics).
Reference: M. Asada, R. Chen, F. Frick, F. Huang, M. Polevy, D. Stoner, L. H. Tsang, and
Z. Wellner, *On Reay's relaxed Tverberg conjecture and generalizations of Conway's thrackle
conjecture*, arXiv:1608.04279.
-/

noncomputable section

namespace Asada2018Reay

open Finset

open scoped Classical in
/-- **Conjecture 4.1**. A planar thrackle of convex hulls with a finite
transversal set has at most as many convex sets as vertices. -/
theorem conjecture_4_1_convex_set_thrackle_bound
    {m : ℕ} (W V : Finset (EuclideanSpace ℝ (Fin 2)))
    (A : Fin m → Finset (EuclideanSpace ℝ (Fin 2)))
    (hV : V ⊆ W)
    (hA_subset : ∀ i : Fin m, A i ⊆ V)
    (hA_nonempty : ∀ i : Fin m, (A i).Nonempty)
    (hdistinct :
      Function.Injective (fun i : Fin m ↦
        convexHull ℝ (A i : Set (EuclideanSpace ℝ (Fin 2)))))
    (hpair : ∀ i j : Fin m, i ≠ j →
      #{p ∈ W | p ∈ convexHull ℝ (A i : Set (EuclideanSpace ℝ (Fin 2))) ∧
        p ∈ convexHull ℝ (A j : Set (EuclideanSpace ℝ (Fin 2)))} = 1) :
    m ≤ #V := by
  sorry

end Asada2018Reay
