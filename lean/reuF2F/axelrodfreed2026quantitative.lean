import Mathlib

/-!
# Quantitative Transversal Theorems in the Plane

Authors: Ilani Axelrod-Freed, Joao Pedro Carvalho, and Yuki Takahashi.
Origin: [NYC Discrete Math REU 2021](https://arxiv.org/pdf/2308.11024v3#page=21).
Reference: I. Axelrod-Freed, J. P. Carvalho, and Y. Takahashi, *Quantitative transversal theorems
in the plane*, Discrete Comput. Geom. (2026); doi:10.1007/s00454-026-00859-1; arXiv:2308.11024v3.
-/

noncomputable section

namespace Axelrodfreed2026Quantitative

open Finset

/-- The space `C(ℝ^d)` of compact convex sets, including the empty set, with the Hausdorff
topology. -/
abbrev CompactConvex (d : ℕ) :=
  {K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) //
    Convex ℝ (K : Set (EuclideanSpace ℝ (Fin d)))}

/-- The part `H^+(C)` in the closed positive half-space of `H`, with normal `v` and offset `t`. -/
def positivePart {d : ℕ} (K : CompactConvex d)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) : CompactConvex d :=
  ⟨⟨(K.val : Set (EuclideanSpace ℝ (Fin d))) ∩ {x | t ≤ inner ℝ v x},
      K.val.isCompact.inter_right (isClosed_le continuous_const (innerSL ℝ v).continuous)⟩,
    K.property.inter (convex_halfSpace_ge (innerSL ℝ v).toLinearMap.isLinear t)⟩

/-- The part `H^-(C)` in the opposite closed half-space. -/
def negativePart {d : ℕ} (K : CompactConvex d)
    (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) : CompactConvex d :=
  ⟨⟨(K.val : Set (EuclideanSpace ℝ (Fin d))) ∩ {x | inner ℝ v x ≤ t},
      K.val.isCompact.inter_right (isClosed_le (innerSL ℝ v).continuous continuous_const)⟩,
    K.property.inter (convex_halfSpace_le (innerSL ℝ v).toLinearMap.isLinear t)⟩

/-- A hyperplane stabs `K` when both closed half-space parts reach the threshold
(Definition 13). -/
def HyperplaneStabs {d : ℕ} (K : CompactConvex d) (f : CompactConvex d → ℝ)
    (α : ℝ) (v : EuclideanSpace ℝ (Fin d)) (t : ℝ) : Prop :=
  α ≤ f (positivePart K v t) ∧ α ≤ f (negativePart K v t)

/-- An `(f, α)`-consistent labeling in `ℝ^k`: small quantitatively separated subfamilies have
disjoint label hulls (Definition 14). The labeling need not be injective or spanning. -/
def HasConsistentOrdering {d : ℕ} (F : Finset (CompactConvex d))
    (f : F → CompactConvex d → ℝ) (α : F → ℝ) (k : ℕ) : Prop :=
  ∃ φ : F → EuclideanSpace ℝ (Fin k),
    ∀ A B : Finset F, #A + #B ≤ k + 2 →
      ∀ v ≠ (0 : EuclideanSpace ℝ (Fin d)), ∀ t : ℝ,
        (∀ i ∈ A, f i (negativePart i.val v t) < α i) →
        (∀ i ∈ B, f i (positivePart i.val v t) < α i) →
        Disjoint (convexHull ℝ (φ '' (A : Set F)))
          (convexHull ℝ (φ '' (B : Set F)))

/-- **Conjecture 6.2**. An `(f, α)`-consistent labeling in any dimension below `d` forces a
quantitative hyperplane transversal, under the standing monotonicity, Hausdorff continuity,
empty-set normalization and individual-direction assumptions. -/
theorem conjecture_6_2
    {d : ℕ} (k : ℕ) (hkd : k < d) (F : Finset (CompactConvex d))
    (f : F → CompactConvex d → ℝ) (α : F → ℝ)
    (hmono : ∀ i, Monotone (f i))
    (hcont : ∀ i, Continuous (f i))
    (hempty : ∀ i, f i ⟨⊥, convex_empty⟩ = 0)
    (hdirections : ∀ (i : F) (v : EuclideanSpace ℝ (Fin d)), v ≠ 0 →
      ∃ t : ℝ, HyperplaneStabs i.val (f i) (α i) v t)
    (hordering : HasConsistentOrdering F f α k) :
    ∃ (v : EuclideanSpace ℝ (Fin d)) (t : ℝ), v ≠ 0 ∧
      ∀ i : F, HyperplaneStabs i.val (f i) (α i) v t := by
  sorry

end Axelrodfreed2026Quantitative
