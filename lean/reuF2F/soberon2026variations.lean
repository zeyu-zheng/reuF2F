import Mathlib

/-!
# Variations of Helly's theorem for convex splinters

Authors: Pablo Soberon and Iris Ye.
Origin: [NYC Discrete Math REU 2024](https://geometrynyc.wixsite.com/home/previous-years).
Reference: P. Soberon and I. Ye, *Variations of Helly's theorem for convex splinters*,
arXiv:2606.23437v1 (2026), 12 pp.
-/

noncomputable section

namespace Soberon2026Variations

/-- A linear partition: a finite union of affine spaces for which every choice of affinely
independent subsets has affinely independent union (Definition 4.1). -/
def IsLinearPartition {d : ℕ} (C : Set (Fin d → ℝ)) : Prop :=
  ∃ (s : ℕ) (A : Fin s → AffineSubspace ℝ (Fin d → ℝ)),
    C = ⋃ i, (A i : Set (Fin d → ℝ)) ∧
    ∀ U : Fin s → Set (Fin d → ℝ),
      (∀ i, U i ⊆ (A i : Set (Fin d → ℝ))) →
      (∀ i, AffineIndependent ℝ (fun x : U i ↦ (x : Fin d → ℝ))) →
      AffineIndependent ℝ (fun x : (⋃ i, U i) ↦ (x : Fin d → ℝ))

/-- **Unnumbered conjecture** (after Theorem 4.4, p. 8). The dual VC dimension of linear
partitions in positive-dimensional real affine space is `d + 1`.

The dual VC dimension is expressed as an attained maximum of the sizes of fully realized
membership patterns. -/
theorem dual_vc_dimension_linear_partitions (d : ℕ) (hd : 0 < d) :
    IsGreatest {m : ℕ | ∃ C : Fin m → Set (Fin d → ℝ),
      (∀ i, IsLinearPartition (C i)) ∧
      let traces : Set (Finset (Fin m)) :=
        {t | ∃ x : Fin d → ℝ, ∀ i, x ∈ C i ↔ i ∈ t}
      (Set.toFinite traces).toFinset.Shatters Finset.univ} (d + 1) := by
  sorry

end Soberon2026Variations
