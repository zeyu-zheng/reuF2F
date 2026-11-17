import Mathlib

/-!
# Numerical sets, core partitions, and integer points in polytopes

Authors: Hannah Constantin, Ben Houston-Edwards, and Nathan Kaplan.
Origin: [Yale SUMRY](https://sumry.yale.edu/past-projects).
Reference: H. Constantin, B. Houston-Edwards, and N. Kaplan, *Numerical sets, core partitions,
and integer points in polytopes*, arXiv:1509.06077.
-/

noncomputable section

namespace Constantin2017Numerical

open Finset

/-- A numerical set is a subset of `ℕ` containing `0` and with finite complement. -/
structure NumericalSet where
  /-- The underlying subset of `ℕ`. -/
  carrier : Set ℕ
  zero_mem : 0 ∈ carrier
  finite_complement : Set.Finite {n : ℕ | n ∉ carrier}

instance : Membership ℕ NumericalSet := ⟨fun T n ↦ n ∈ T.carrier⟩

/-- A numerical set is a numerical semigroup when it is closed under addition. -/
def NumericalSet.IsNumericalSemigroup (T : NumericalSet) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, x + y ∈ T

open scoped Classical in
/-- The profile bijection relation `φ(T) = λ`. With the gaps of `T` in decreasing order, the row
for a gap `n` has length `#{t ∈ T : t < n}`. -/
def Phi (T : NumericalSet) (lam : YoungDiagram) : Prop :=
  ∃ gapList : List ℕ,
    gapList.Nodup ∧
      (∀ n : ℕ, n ∈ gapList ↔ n ∉ T) ∧
      gapList.Pairwise (fun m n ↦ n < m) ∧
      lam.rowLens =
        gapList.map (fun n : ℕ ↦ #{t ∈ Finset.range n | t ∈ T})

open Filter
open scoped Topology

open scoped Classical in
/-- **Conjecture 8.1**. If `P(n)` counts partitions of size at most `n` and `S'(n)` counts those
associated via `φ` to numerical semigroups, then `S'(n) / P(n) → 0`. -/
theorem conjecture_8_1_semigroup_associated_partitions_density_zero :
    Tendsto
      (fun n : ℕ ↦
        let partitions := Finset.univ.biUnion (fun k : Fin (n + 1) ↦
          Finset.univ.image (fun p : Nat.Partition k.val ↦ YoungDiagram.ofPartition p))
        ((#{lam ∈ partitions |
            ∃ T : NumericalSet, T.IsNumericalSemigroup ∧ Phi T lam} : ℝ) /
          (#partitions : ℝ)))
      atTop (𝓝 0) := by sorry

end Constantin2017Numerical
