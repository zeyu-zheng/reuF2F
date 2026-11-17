import Mathlib

/-!
# Friezes over Z[sqrt(2)]

Authors: Esther Banaian, Libby Farrell, Amy Tao, Kayla Wright, and Joy Zhichun Zhang.
Origin: [University of Minnesota Twin Cities REU
2021](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: E. Banaian, L. Farrell, A. Tao, K. Wright, and J. Z. Zhang, *Friezes over
Z[sqrt(2)]*, arXiv:2307.00440v2.
-/

noncomputable section

namespace Banaian2023Friezes

open Finset

/-- A polygon dissection, represented by its noncrossing arcs together with every boundary edge
(Section 2.2). -/
def IsDissection {n : ℕ} (D : SimpleGraph (Fin n)) : Prop :=
  (∀ i, D.Adj i (finRotate n i)) ∧
    ∀ a b c d, sbtw a b c → sbtw c d a →
      D.Adj a c → ¬D.Adj b d

open scoped Classical in
/-- The subpolygons of a dissection: its chordless cycles, represented by
their vertex sets in the inherited cyclic order. -/
def cells {n : ℕ} (D : SimpleGraph (Fin n)) : Finset (Finset (Fin n)) :=
  {S | 3 ≤ #S ∧ (D.induce (S : Set (Fin n))).Connected ∧
    ∀ v, (D.induce (S : Set (Fin n))).degree v = 2}

open scoped Classical in
/-- The frieze of a triangle/quadrilateral dissection (Section 2.2). Entries are continuant
determinants of the incident-polygon quiddity. -/
def friezeEntry {n : ℕ} (D : SimpleGraph (Fin n)) (i j : Fin n) : Zsqrtd 2 :=
  let lo := min i.val j.val
  let hi := max i.val j.val
  if i = j then 0 else
    Matrix.det fun a b : Fin (hi - lo - 1) ↦
      if a = b then
        let v : Fin n := ⟨lo + a.val + 1, by dsimp [lo, hi] at *; omega⟩
        (#{S ∈ cells D | v ∈ S ∧ #S = 3} : Zsqrtd 2) +
          (#{S ∈ cells D | v ∈ S ∧ #S = 4} : Zsqrtd 2) *
            Zsqrtd.sqrtd
      else if a.val + 1 = b.val ∨ b.val + 1 = a.val then 1 else 0

/-- **Conjecture 1**. A triangle/quadrilateral dissection produces a unitary
frieze exactly when it is a gluing of towers. -/
theorem conjecture_1 {n : ℕ} (hn : 3 ≤ n) (D : SimpleGraph (Fin n))
    (hD : IsDissection D)
    (hpieces : ∀ S ∈ cells D, #S = 3 ∨ #S = 4) :
    (∃ T : SimpleGraph (Fin n),
      IsDissection T ∧ (∀ S ∈ cells T, #S = 3) ∧
        ∀ i j, T.Adj i j → IsUnit (friezeEntry D i j)) ↔
    (∃ C : SimpleGraph (Fin n),
      IsDissection C ∧ C ≤ D ∧ ∀ S ∈ cells C,
        #{F ∈ {F ∈ cells D | F ⊆ S} | #F = 3} = 1 ∧
          ∀ v ∈ S, #{F ∈ {F ∈ cells D | F ⊆ S} | v ∈ F} ≤ 2) := by
  sorry

end Banaian2023Friezes
