import Mathlib

/-!
# K-Knuth Equivalence for Increasing Tableaux

Authors: Christian Gaetz, Michelle Mastrianni, Rebecca Patrias, Hailee Peck,
Colleen Robichaux, David Schwein, and Ka Yu Tam.
Origin: [University of Minnesota Twin Cities REU
2014](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: C. Gaetz, M. Mastrianni, R. Patrias, H. Peck, C. Robichaux, D. Schwein, and K. Y. Tam,
*K-Knuth equivalence for increasing tableaux*, Electron. J. Combin. **23** (2016), no. 1,
Paper 1.40; arXiv:1409.6659v2.
-/

namespace Gaetz2016K

/-- A straight increasing tableau with positive integer labels (Section 2.1). -/
structure IncreasingTableau where
  /-- The Young diagram giving the straight shape. -/
  shape : YoungDiagram
  /-- The positive integer label in each box of the shape. -/
  entry : {b : ℕ × ℕ // b ∈ shape} → ℕ+
  increasing : ∀ a b, a.val ≤ b.val → a.val ≠ b.val → entry a < entry b

/-- The reading word: each row left to right, starting at the bottom row (Section 2.4). -/
noncomputable def rowWord (T : IncreasingTableau) : List ℕ+ :=
  ((T.shape.cells.attach.toList.mergeSort fun a b ↦
    decide (b.val.1 < a.val.1 ∨ (a.val.1 = b.val.1 ∧ a.val.2 ≤ b.val.2))).map
      (fun b ↦ T.entry ⟨b.val, b.property⟩))

/-- The four K-Knuth moves in an arbitrary word context (Section 2.3). -/
inductive KKnuthMove : List ℕ+ → List ℕ+ → Prop
  | duplicate (u v : List ℕ+) (x : ℕ+) :
      KKnuthMove (u ++ [x] ++ v) (u ++ [x, x] ++ v)
  | braid (u v : List ℕ+) (x y : ℕ+) :
      KKnuthMove (u ++ [x, y, x] ++ v) (u ++ [y, x, y] ++ v)
  | firstKnuth (u v : List ℕ+) (x y z : ℕ+) (hxy : x < y) (hyz : y < z) :
      KKnuthMove (u ++ [x, z, y] ++ v) (u ++ [z, x, y] ++ v)
  | secondKnuth (u v : List ℕ+) (x y z : ℕ+) (hxy : x < y) (hyz : y < z) :
      KKnuthMove (u ++ [y, x, z] ++ v) (u ++ [y, z, x] ++ v)

/-- **Conjecture 4.3** (arXiv; published Conjecture 57). Equivalent tableaux can be connected
through words no longer than the largest tableau in their entire K-Knuth class. -/
theorem conjecture_4_3 (T T' : IncreasingTableau)
    (h : Relation.EqvGen KKnuthMove (rowWord T) (rowWord T')) :
    ∃ k : ℕ,
      IsGreatest {m : ℕ | ∃ U : IncreasingTableau,
        Relation.EqvGen KKnuthMove (rowWord T) (rowWord U) ∧ U.shape.card = m} k ∧
      ∃ path : List (List ℕ+),
        path.head? = some (rowWord T) ∧ path.getLast? = some (rowWord T') ∧
        path.IsChain (Relation.SymmGen KKnuthMove) ∧
        ∀ w ∈ path, w.length ≤ k := by
  sorry

end Gaetz2016K
