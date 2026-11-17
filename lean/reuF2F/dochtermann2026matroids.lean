import Mathlib

/-!
# Matroids with cycle systems are regular

Authors: Anton Dochtermann, Evan Huang, Kai Mawhinney, Suho Oh, and Yuchen Xu.
Origin: [Texas State University REU 2025](https://summerreu.wp.txstate.edu/home/123-2/).
Reference: A. Dochtermann, E. Huang, K. Mawhinney, S. Oh, and Y. Xu, *Matroids with cycle systems
are regular*, arXiv:2609.13361v1 (2026), 23 pp.
-/

noncomputable section

namespace Dochtermann2026Matroids

open Finset

/-- The elements lying in exactly one member of the collection (Definition 2.13). -/
def uniqueUnion {α : Type*} (C : Finset (Set α)) : Set α :=
  {e | ∃! A, A ∈ C ∧ e ∈ A}

/-- A corank-sized set of circuits whose every nonempty subcollection has dependent unique union
(Definition 2.14 and p. 8). -/
def IsCircuitSystem {α : Type*} (M : Matroid α) (C : Finset (Set α)) : Prop :=
  #C = M.E.ncard - M.eRank.toNat ∧
    (∀ A ∈ C, M.IsCircuit A) ∧
    ∀ D : Finset (Set α), D ⊆ C → D.Nonempty → M.Dep (uniqueUnion D)

open scoped Classical in
/-- **Conjecture 7.5**. If the total unique union of a circuit system is a circuit, then the ground
elements contained in at least three system circuits are independent. -/
theorem conjecture_7_5 {α : Type*} (M : Matroid α) [M.Finite]
    (C : Finset (Set α)) (hC : IsCircuitSystem M C)
    (hUnion : M.IsCircuit (uniqueUnion C)) :
    M.Indep {e ∈ M.E | 3 ≤ #{A ∈ C | e ∈ A}} := by
  sorry

end Dochtermann2026Matroids
