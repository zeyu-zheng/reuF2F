import Mathlib

/-!
# Extreme Genera and Other Techniques of Graph Embeddings

Authors: Eion Blanchard and Esther Hunt.
Origin: [University of Washington REU 2016](https://sites.math.washington.edu/~reu/papers/2016/).
Reference: E. Blanchard and E. Hunt, *Extreme genera and other techniques of graph embeddings*,
University of Washington REU report (2016), 25 pp.
-/

noncomputable section

namespace Blanchard2016Extreme

/-- The appended 3-to-1 graph: the labeled graph of p. 4 with vertex `14` joined to the fourteen
boundary vertices (Section 1.1, Definition 1.5). -/
def appendedThreeToOne : SimpleGraph (Fin 23) :=
  SimpleGraph.fromRel fun u v ↦
    (u = 14 ∧ v < 14) ∨
    (u = 15 ∧ v ∈ ({0, 1, 12, 13} : Finset (Fin 23))) ∨
    (u = 16 ∧ v ∈ ({5, 6, 12, 13} : Finset (Fin 23))) ∨
    (u = 17 ∧ v ∈ ({0, 1, 2, 3} : Finset (Fin 23))) ∨
    (u = 18 ∧ v ∈ ({2, 3, 4, 5} : Finset (Fin 23))) ∨
    (u = 19 ∧ v ∈ ({4, 5, 6, 7} : Finset (Fin 23))) ∨
    (u = 20 ∧ v ∈ ({4, 6, 8, 9} : Finset (Fin 23))) ∨
    (u = 21 ∧ v ∈ ({0, 8, 9, 10} : Finset (Fin 23))) ∨
    (u = 22 ∧ v ∈ ({0, 1, 10, 11} : Finset (Fin 23))) ∨
    (u = 1 ∧ v = 10)

/-- A rotation system: a cyclic ordering of the neighbors of each vertex (Definition 2.15). Without
edge signatures it describes only orientable embeddings (Remark 2.17). -/
structure RotationSystem {V : Type*} (G : SimpleGraph V) where
  /-- The cyclic permutation of the neighbors of each vertex. -/
  rotation : (v : V) → Equiv.Perm (G.neighborSet v)
  cyclic : ∀ v, (rotation v).IsCycleOn Set.univ

/-- The dart successor tracing the oriented face boundaries in Section 2.3. -/
def RotationSystem.facePermutation {V : Type*} {G : SimpleGraph V}
    (r : RotationSystem G) : Equiv.Perm G.Dart where
  toFun d :=
    let w := r.rotation d.snd (Subtype.mk d.fst d.adj.symm)
    { toProd := (d.snd, w.val), adj := w.property }
  invFun d :=
    let w := (r.rotation d.fst).symm (Subtype.mk d.snd d.adj)
    { toProd := (w.val, d.fst), adj := w.property.symm }
  left_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · exact congrArg Subtype.val
        ((r.rotation d.snd).symm_apply_apply (Subtype.mk d.fst d.adj.symm))
    · rfl
  right_inv d := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((r.rotation d.fst).apply_symm_apply (Subtype.mk d.snd d.adj))

/-- **Conjecture 1.13**. The 3-to-1 graph is 3-circular, equivalently its appended graph has
minimum orientable genus three.

Face cycles and the Euler equation are those of Section 2.3; the boundary order is not
prescribed. -/
theorem conjecture_1_13 :
    let eulerCharacteristic := fun r : RotationSystem appendedThreeToOne ↦
      (Nat.card (Fin 23) : ℤ) - Nat.card appendedThreeToOne.edgeSet +
        Nat.card (Quotient (Equiv.Perm.SameCycle.setoid r.facePermutation))
    (∃ r : RotationSystem appendedThreeToOne,
      eulerCharacteristic r = 2 - 2 * 3) ∧
      (∀ r : RotationSystem appendedThreeToOne,
        eulerCharacteristic r ≤ 2 - 2 * 3) := by
  sorry

end Blanchard2016Extreme
