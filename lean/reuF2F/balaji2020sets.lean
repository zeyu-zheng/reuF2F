import Mathlib

/-!
# Sets in R^d determining k taxicab distances

Authors: Vajresh Balaji, Olivia Edwards, Anne Marie Loftin, Solomon Mcharo, Lo Phillips,
Alex Rice, and Bineyam Tsegaye.
Origin: [Millsaps College Kinnaird Institute Research Experience
2019](https://millsaps.edu/inaugural-kinnaird-institute-research-experience/).
Reference: V. Balaji, O. Edwards, A. M. Loftin, S. Mcharo, L. Phillips, A. Rice, and B. Tsegaye,
*Sets in R^d determining k taxicab distances*, Involve **13** (2020), 487-509.
-/

namespace Balaji2020Sets

/-- Integer points of taxicab norm at most `k` whose coordinate sum has the parity of `k`,
embedded in real taxicab space (Definition 2.1). -/
def latticePoints (d k : ℕ) : Set (PiLp 1 (fun _ : Fin d ↦ ℝ)) :=
  {x | ∃ z : Fin d → ℤ,
    (∀ i, x i = (z i : ℝ)) ∧
    (∑ i, (z i).natAbs) ≤ k ∧
    (∑ i, z i) % 2 = (k : ℤ) % 2}

/-- `ℓ¹`-similarity by translations, coordinate reflections, uniform nonzero scaling and
coordinate permutations (Definition 2.4). -/
def L1Similar {d : ℕ} (P Q : Set (PiLp 1 (fun _ : Fin d ↦ ℝ))) : Prop :=
  ∃ (a : PiLp 1 (fun _ : Fin d ↦ ℝ)) (r : ℝ), 0 < r ∧
    ∃ (σ : Equiv.Perm (Fin d)) (signs : Fin d → Bool),
      Q = (fun x : PiLp 1 (fun _ : Fin d ↦ ℝ) ↦
        WithLp.toLp 1 (fun i ↦ a i + r * (if signs i then 1 else -1) * x (σ i))) '' P

/-- **Conjecture 2.7** (arXiv v3, p. 4; published p. 491). The parity-restricted integer
taxicab ball is, up to `ℓ¹`-similarity, the unique largest configuration with at most `k` nonzero
distances. -/
theorem conjecture_2_7 {d : ℕ} (k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (P : Set (PiLp 1 (fun _ : Fin d ↦ ℝ)))
    (hP : {r : ℝ | ∃ x ∈ P, ∃ y ∈ P, x ≠ y ∧ dist x y = r}.encard ≤ k) :
    P.encard ≤ (latticePoints d k).encard ∧
      (P.encard = (latticePoints d k).encard ↔ L1Similar P (latticePoints d k)) := by
  sorry

end Balaji2020Sets
