import Mathlib

/-!
# Clones of Borel Boolean Functions

Authors: Ruiyuan Chen and Ilir Ziba.
Origin: [University of Michigan REU
2023](https://prod.lsa.umich.edu/content/dam/math-assets/reu-su22/reu-2023/Ziba,%20Ilir_REU_2023.pdf).
Reference: R. Chen and I. Ziba, *Clones of Borel Boolean functions*, revised author manuscript
(2026), 59 pp.; arXiv:2407.06719; https://rynchn.github.io/math/borelclone.pdf.
-/

namespace Chen2026Clones

/-- Arity indices: `none` is countably infinite arity and `some k` is arity `k + 1`
(Conventions 2.3 and 2.23). Nullary operations are excluded. -/
def ArityIndex : Option ℕ → Type
  | none => ℕ
  | some k => Fin (k + 1)

/-- A Borel clone: a family of Borel Boolean operations containing all projections and closed
under arity-compatible substitution (Definitions 2.5 and 4.1). -/
structure BorelClone where
  /-- The operations of each arity belonging to the clone. -/
  operations : (a : Option ℕ) → Set ((ArityIndex a → Bool) → Bool)
  measurable_mem : ∀ a f, f ∈ operations a → Measurable f
  projection_mem : ∀ a (i : ArityIndex a), (fun x ↦ x i) ∈ operations a
  substitution_mem : ∀ (a b : Option ℕ)
    (g : (ArityIndex a → Bool) → Bool)
    (fs : ArityIndex a → (ArityIndex b → Bool) → Bool),
    g ∈ operations a → (∀ i, fs i ∈ operations b) →
      (fun x ↦ g (fun i ↦ fs i x)) ∈ operations b

/-- **Conjecture 1.5** (revised author manuscript). At least continuum many distinct Borel clones
have as finitary part exactly the finite operations preserving binary meet, zero and one. -/
theorem conjecture_1_5 :
    Cardinal.continuum ≤ Cardinal.mk {C : BorelClone //
      ∀ k : ℕ, ∀ f : (Fin (k + 1) → Bool) → Bool,
        f ∈ C.operations (some k) ↔
          ∃ h : InfTopHom (Fin (k + 1) → Bool) Bool,
            ⇑h = f ∧ h (fun _ ↦ false) = false} := by
  sorry

end Chen2026Clones
