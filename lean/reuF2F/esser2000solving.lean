import Mathlib

/-!
# On Solving the Inverse Conductivity Problem for Annular Networks

Author: Ernie Esser.
Origin: [University of Washington REU 2000](https://sites.math.washington.edu/~reu/papers/2000/).
Reference: E. Esser, *On Solving the Inverse Conductivity Problem for Annular Networks*,
August 2000 (appendix added 2005).
-/

noncomputable section

namespace Esser2000Solving

open scoped Classical in
/-- The pairwise conductance, summing over all edges with the two given ends, parallel edges
included (Curtis-Morrow, p. 27). -/
def conductance {V E : Type*} [Fintype E] (G : Graph V E) (w : E → ℝ) :
    Matrix V V ℝ :=
  fun x y ↦ ∑ e, if G.IsLink e x y then w e else 0

open scoped Classical in
/-- The weighted Kirchhoff matrix (Esser p. 3; Curtis-Morrow pp. 33-34). Loop contributions
cancel on the diagonal. -/
def kirchhoff {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (w : E → ℝ) : Matrix V V ℝ :=
  Matrix.diagonal (fun x ↦ ∑ y, conductance G w x y) - conductance G w

open scoped Classical in
/-- The response matrix on the six boundary labels, given by the Schur complement formula
(Esser p. 3; Curtis-Morrow pp. 42-43). -/
def response {I E : Type*} [Fintype I] [Fintype E]
    (G : Graph (Fin 6 ⊕ I) E) (w : E → ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  let K := kirchhoff G w
  K.submatrix Sum.inl Sum.inl -
    K.submatrix Sum.inl Sum.inr * (K.submatrix Sum.inr Sum.inr)⁻¹ *
      K.submatrix Sum.inr Sum.inl

/-- Esser's graph G(3,2) with the fifteen edges of pp. 32-33 (Figure 3). Source vertices
1, ..., 12 are `Sum.inl 0`, ..., `Sum.inl 5`, `Sum.inr 0`, ..., `Sum.inr 5` in order. -/
def annularGraph : Graph (Fin 6 ⊕ Fin 6) (Fin 15) :=
  let ends : Fin 15 → (Fin 6 ⊕ Fin 6) × (Fin 6 ⊕ Fin 6) :=
    ![(Sum.inl 0, Sum.inr 0), (Sum.inl 1, Sum.inr 1), (Sum.inl 2, Sum.inr 2),
      (Sum.inl 3, Sum.inr 3), (Sum.inl 4, Sum.inr 4), (Sum.inl 5, Sum.inr 5),
      (Sum.inr 0, Sum.inr 1), (Sum.inr 1, Sum.inr 2), (Sum.inr 0, Sum.inr 2),
      (Sum.inr 3, Sum.inr 4), (Sum.inr 4, Sum.inr 5), (Sum.inr 3, Sum.inr 5),
      (Sum.inr 0, Sum.inr 3), (Sum.inr 1, Sum.inr 4), (Sum.inr 2, Sum.inr 5)]
  { vertexSet := Set.univ
    edgeSet := Set.univ
    IsLink := fun e x y ↦ (x = (ends e).1 ∧ y = (ends e).2) ∨
      (x = (ends e).2 ∧ y = (ends e).1)
    isLink_symm := by
      intro e _
      exact ⟨fun x y h ↦ h.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
        (fun h ↦ Or.inl ⟨h.2, h.1⟩)⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro e x y v z h h'
      exact h.elim
        (fun h ↦ h'.elim (fun h' ↦ Or.inl (h.1.trans h'.1.symm))
          (fun h' ↦ Or.inr (h.1.trans h'.2.symm)))
        (fun h ↦ h'.elim (fun h' ↦ Or.inr (h.1.trans h'.2.symm))
          (fun h' ↦ Or.inl (h.1.trans h'.1.symm)))
    edge_mem_iff_exists_isLink := by
      intro e
      constructor
      · intro _
        exact ⟨(ends e).1, (ends e).2, Or.inl ⟨rfl, rfl⟩⟩
      · intro _
        trivial
    left_mem_of_isLink := by intros; trivial }

/-- **Conjecture 4.1** (p. 18; inequality list p. 13). A finite positive six-boundary W2
network has a response realizable by positive conductances on G(3,2) if and only if the cubic
relation and all thirteen ordered strict minor inequalities hold.

Boundary label `k + 1` is `Sum.inl k`, and all `Sum.inr` vertices are interior. Loops and
parallel edges are allowed and every component meets the boundary; no embedding, global
connectedness or nonempty interior is required (Curtis-Morrow, pp. 11, 27, 30 and 39). -/
theorem conjecture_4_1 {I E : Type*} [Fintype I] [Fintype E]
    (G : Graph (Fin 6 ⊕ I) E)
    (hV : G.vertexSet = Set.univ) (hE : G.edgeSet = Set.univ)
    (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (hW2 : ∀ v, ∃ b : Fin 6,
      Relation.ReflTransGen G.Adj v (Sum.inl b)) :
    let L := response G w
    (∃ γ : Fin 15 → ℝ, (∀ e, 0 < γ e) ∧ response annularGraph γ = L) ↔
      (L.submatrix ![0, 1, 3] ![2, 4, 5]).det -
        (L.submatrix ![0, 3, 4] ![1, 2, 5]).det = 0 ∧
      (L.submatrix ![0, 1, 2] ![3, 4, 5]).det < 0 ∧
      0 < (L.submatrix ![0, 1, 4] ![2, 3, 5]).det ∧
      0 < (L.submatrix ![1, 0, 3] ![2, 4, 5]).det ∧
      0 < (L.submatrix ![1, 2, 4] ![0, 3, 5]).det ∧
      0 < (L.submatrix ![1, 2, 5] ![0, 4, 3]).det ∧
      0 < (L.submatrix ![0, 2, 3] ![1, 4, 5]).det ∧
      0 < (L.submatrix ![0, 2, 5] ![1, 3, 4]).det ∧
      0 < (L.submatrix ![0, 1] ![3, 4]).det ∧
      0 < (L.submatrix ![1, 2] ![4, 5]).det ∧
      0 < (L.submatrix ![0, 2] ![3, 5]).det ∧
      0 < (L.submatrix ![0, 3] ![1, 4]).det ∧
      0 < (L.submatrix ![0, 3] ![2, 5]).det ∧
      0 < (L.submatrix ![1, 4] ![2, 5]).det := by
  sorry

end Esser2000Solving
