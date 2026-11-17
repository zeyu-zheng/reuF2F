import Mathlib

/-!
# Zonotopes whose cellular strings are all coherent

Authors: Rob Edman, Pakawut Jiradilok, Gaku Liu, and Thomas McConville.
Origin: [University of Minnesota Twin Cities REU
2015](https://www-users.cse.umn.edu/~reiner/REU/REU2015notes/REU2015salvage.html).
Reference: R. Edman, P. Jiradilok, G. Liu, and T. McConville, *Zonotopes whose cellular strings
are all coherent*, arXiv:1801.09140v1 (2018).
-/

noncomputable section

namespace Edman2021Zonotopes

open Finset

/-- A reduced antipodal gallery, encoded by its crossing order (Section 3.2). Every prefix is a
realizable chamber, with forms oriented positively on the fundamental chamber. -/
def Gallery {n m : ℕ} (a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) :=
  {σ : Equiv.Perm (Fin m) // ∀ k : Fin (m + 1), ∃ x : Fin n → ℝ,
    ∀ j : Fin m, if j.val < k.val then a (σ j) x < 0 else 0 < a (σ j) x}

open scoped Classical in
/-- The codimension-two intersection flats, counted as subspaces, not as choices of generating
hyperplanes (Section 3.2). -/
def rankTwoFlats {n m : ℕ} (a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    Finset (Submodule ℝ (Fin n → ℝ)) :=
  {X ∈ (Finset.univ : Finset (Fin m)).powerset.image
      (fun S ↦ ⨅ i ∈ S, LinearMap.ker (a i)) |
    Module.finrank ℝ ((Fin n → ℝ) ⧸ X) = 2}

open scoped Classical in
/-- The localization: the crossing order of hyperplanes containing the given intersection flat
(Section 3.2). -/
def localizedGallery {n m : ℕ} {a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ}
    (X : Submodule ℝ (Fin n → ℝ)) (γ : Gallery a) : List (Fin m) :=
  (List.ofFn γ.val).filter (fun i ↦ decide (X ≤ LinearMap.ker (a i)))

open scoped Classical in
/-- The L2-separation set of two reduced galleries (Section 3.2). -/
def separationSet {n m : ℕ} {a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ}
    (γ γ' : Gallery a) : Finset (Submodule ℝ (Fin n → ℝ)) :=
  {X ∈ rankTwoFlats a | localizedGallery X γ ≠ localizedGallery X γ'}

/-- Two galleries are adjacent exactly when their L2-separation set has cardinality one
(Remark 3.3). -/
def galleryGraph {n m : ℕ} (a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    SimpleGraph (Gallery a) where
  Adj γ γ' := #(separationSet γ γ') = 1
  symm := by
    constructor
    intro γ γ' h
    simpa only [separationSet, ne_comm] using h
  loopless := by
    constructor
    intro γ
    simp [separationSet]

/-- A cellular string: an ordered partition into nonempty blocks, each with a realizable face
vanishing exactly on its block (Section 3.2). The empty partition is the trivial string. -/
structure CellularString {n m : ℕ} (a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ) where
  /-- The number of blocks of the ordered partition. -/
  blocks : ℕ
  /-- The block containing each hyperplane index. -/
  block : Fin m → Fin blocks
  onto : Function.Surjective block
  realizable : ∀ k : Fin blocks, ∃ x : Fin n → ℝ,
    (∀ i, block i < k → a i x < 0) ∧
    (∀ i, block i = k → a i x = 0) ∧
    (∀ i, k < block i → 0 < a i x)

/-- **Remark 3.3**. All-pairs gallery distance equal to L2-separation cardinality implies
all-coherence.

Coherence uses the cellular-string and block-ratio description of Section 3.2 and Lemma 3.2,
the source's halfspace names are swapped, and no rank or essentiality restriction is imposed. -/
theorem remark_3_3 {n m : ℕ} (a : Fin m → (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (hhyperplanes : ∀ i, a i ≠ 0)
    (hdistinct : Function.Injective (fun i ↦ LinearMap.ker (a i)))
    (b : Fin n → ℝ) (hchamber : ∀ i, 0 < a i b)
    (hdistance : ∀ γ γ' : Gallery a,
      (galleryGraph a).edist γ γ' = (#(separationSet γ γ') : ℕ∞)) :
    ∃ π : Fin n → ℝ, (∀ i, 0 < a i π) ∧
      ∀ s : CellularString a, ∃ ψ : Fin n → ℝ,
        (∀ i j, s.block i = s.block j → a i ψ / a i π = a j ψ / a j π) ∧
        (∀ i j, s.block i < s.block j → a i ψ / a i π < a j ψ / a j π) := by
  sorry

end Edman2021Zonotopes
