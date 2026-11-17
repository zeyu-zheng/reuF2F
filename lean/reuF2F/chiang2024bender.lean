import Mathlib

/-!
# Bender-Knuth involutions on linear extensions of posets

Authors: Judy Hsin-Hui Chiang, Anh Trong Nam Hoang, Matthew Kendall,
Ryan Lynch, Son Nguyen, Benjamin Przybocki, and Janabel Xia.
Origin: [University of Minnesota Twin Cities REU
2022](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: J. H.-H. Chiang, A. T. N. Hoang, M. Kendall, R. Lynch, S. Nguyen, B. Przybocki, and
J. Xia, *Bender-Knuth involutions on linear extensions of posets*, Discrete Math. **347** (2024),
no. 9, 114068; arXiv:2302.12425v2.
-/

namespace Chiang2024Bender

/-- The double-tailed diamond `d_k(1)`: two chains of `k - 2` elements separated by two
incomparable elements ([PS19], Section 2). -/
abbrev DoubleTailedDiamond (k : ℕ) : Type :=
  Lex (Lex (Fin (k - 2) ⊕ (PUnit ⊕ PUnit)) ⊕ Fin (k - 2))

/-- The `d_k`-minus shape: `d_k(1)` without its greatest element ([PS19], Section 6). -/
abbrev DiamondMinus (k : ℕ) := {x : DoubleTailedDiamond k // ¬IsMax x}

/-- A convex embedded `d_k`-minus set ([PS19], Section 6). -/
def IsDiamondMinusSet {P : Type*} [PartialOrder P] (k : ℕ) (s : Set P) : Prop :=
  s.OrdConnected ∧ Nonempty (DiamondMinus k ≃o s)

/-- The three d-complete axioms ([PS19], Sections 6 and 9), in the root-at-minimum orientation
of Section 3.3. -/
def IsDComplete (P : Type*) [PartialOrder P] : Prop :=
  ∀ k ≥ 3,
    (∀ s : Set Pᵒᵈ, IsDiamondMinusSet k s →
      ∃ z : Pᵒᵈ, z ∉ s ∧
        ∃ a : Pᵒᵈ, s ∪ {z} = Set.Icc a z ∧
          Nonempty (DoubleTailedDiamond k ≃o {x : Pᵒᵈ // x ∈ s ∪ {z}})) ∧
    (∀ a b : Pᵒᵈ,
      Nonempty (DoubleTailedDiamond k ≃o Set.Icc a b) →
        ∀ x : Pᵒᵈ, x ⋖ b → x ∈ Set.Icc a b) ∧
    ∀ s t : Set Pᵒᵈ,
      IsDiamondMinusSet k s → IsDiamondMinusSet k t →
        ∀ a b : Pᵒᵈ, IsLeast s a → IsLeast t b →
          s \ {a} = t \ {b} → s = t

open scoped Classical in
/-- The Bender-Knuth involution `t_i`: swap adjacent labels exactly when their elements are
incomparable (Definition 2.5). Labels are zero-based while `i` is one-based, and outside the
source range the map is the identity. -/
noncomputable def bk {P : Type*} [PartialOrder P] {n : ℕ}
    (i : ℕ) (L : P ≃ Fin n) : P ≃ Fin n :=
  if h : 0 < i ∧ i < n then
    let a : Fin n := { val := i - 1, isLt := lt_of_le_of_lt (Nat.sub_le i 1) h.2 }
    let b : Fin n := { val := i, isLt := h.2 }
    if ¬L.symm a ≤ L.symm b ∧ ¬L.symm b ≤ L.symm a then
      L.trans (Equiv.swap a b)
    else L
  else L

/-- Partial promotion `∂_i = t_i ⋯ t_1`, acting right first (Section 2.2). -/
noncomputable def promotion {P : Type*} [PartialOrder P] {n : ℕ}
    (i : ℕ) (L : P ≃ Fin n) : P ≃ Fin n :=
  (List.range i).foldl (fun M j ↦ bk (j + 1) M) L

/-- Partial evacuation `q_i = ∂_0 ∂_1 ⋯ ∂_i` (Section 2.2). -/
noncomputable def evacuation {P : Type*} [PartialOrder P] {n : ℕ}
    (i : ℕ) (L : P ≃ Fin n) : P ≃ Fin n :=
  (List.range (i + 1)).foldr (fun j M ↦ promotion j M) L

/-- **Conjecture 3.24**. All cactus relations hold on the linear extensions of every finite
d-complete poset, in the root-at-minimum convention. -/
theorem conjecture_3_24 {P : Type*} [PartialOrder P] [Fintype P]
    (hP : IsDComplete P) (i j k : ℕ) (hi : 0 < i)
    (hij : i + 1 < j) (hjk : j < k) (hk : k ≤ Fintype.card P)
    (L : P ≃ Fin (Fintype.card P)) (hL : StrictMono L) :
    let q := fun M : P ≃ Fin (Fintype.card P) ↦
      evacuation (k - 1) (evacuation (k - j) (evacuation (k - 1) M))
    bk i (q (bk i (q L))) = L := by
  sorry

end Chiang2024Bender
