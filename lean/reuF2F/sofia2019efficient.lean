import Mathlib

/-!
# An Efficient Way of Understanding the Maximum Number of Steady-State Solutions for Chemical Reaction Networks
for Chemical Reaction Networks

Author: Dilruba Sofia.
Origin: [Texas A&M University REU
2019](https://artsci.tamu.edu/mathematics/_files/_docs/reu/results/2019/sofia-report.pdf).
Reference: D. Sofia, *An Efficient Way of Understanding the Maximum Number of Steady-State
Solutions for Chemical Reaction Networks*, Texas A&M REU report (July 25, 2019).
-/

noncomputable section

namespace Sofia2019Efficient

open scoped Pointwise
open Finset

/-- A reaction network: finite distinct complexes and distinct directed reactions between them,
with no diagonal reactions. -/
structure Network (n : ℕ) where
  /-- The finite set of complexes. -/
  complexes : Finset (Fin n →₀ ℕ)
  /-- The directed reactions between complexes. -/
  reactions : Finset (complexes × complexes)
  noLoops : ∀ e ∈ reactions, e.1 ≠ e.2

open scoped Classical in
/-- Full reversibilization: every missing reverse reaction is added on the same species and
complexes. -/
def Network.fullyReversible {n : ℕ} (G : Network n) : Network n where
  complexes := G.complexes
  reactions := G.reactions ∪ G.reactions.image Prod.swap
  noLoops := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact G.noLoops e he
    · rcases Finset.mem_image.mp he with ⟨f, hf, rfl⟩
      exact Ne.symm (G.noLoops f hf)

/-- The real stoichiometric subspace spanned by the complete reaction vectors. -/
def Network.stoichiometric {n : ℕ} (G : Network n) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun e : G.reactions ↦
    WithLp.toLp 2 (fun i ↦ (e.val.2.val i : ℝ) - (e.val.1.val i : ℝ)))

open scoped Classical in
/-- The mass-action species polynomials. The coefficient ring may hold actual rates or
unspecialized rate parameters. -/
def Network.massAction {n : ℕ} (G : Network n) {R : Type*} [CommRing R]
    (rates : G.reactions → R) (i : Fin n) : MvPolynomial (Fin n) R :=
  ∑ e : G.reactions,
    MvPolynomial.monomial e.val.1.val
      (rates e * ((e.val.2.val i : R) - (e.val.1.val i : R)))

open scoped Classical in
/-- The conservation-augmented system. Rates and totals are symbolic coefficient variables and
species are the outer variables. -/
def Network.augmentedSystem {n d : ℕ} (G : Network n)
    (W : Matrix (Fin d) (Fin n) ℝ) (pivot : OrderEmbedding (Fin d) (Fin n))
    (i : Fin n) :
    MvPolynomial (Fin n) (MvPolynomial (G.reactions ⊕ Fin d) ℝ) :=
  if h : ∃ r, pivot r = i then
    (∑ j : Fin n,
      MvPolynomial.C (MvPolynomial.C (W (Classical.choose h) j)) *
        MvPolynomial.X j) -
      MvPolynomial.C (MvPolynomial.X (Sum.inr (Classical.choose h)))
  else G.massAction (fun e ↦ MvPolynomial.X (Sum.inl e)) i

open scoped Classical in
/-- The BKK mixed volume of the generic augmented supports (equation (7)). This polarization
has no division by the factorial of the dimension. -/
def Network.mixedVolume {n d : ℕ} (G : Network n)
    (W : Matrix (Fin d) (Fin n) ℝ) (pivot : OrderEmbedding (Fin d) (Fin n)) :
    ℝ :=
  let P : Fin n → TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)) :=
    fun i ↦
      { carrier := convexHull ℝ
          ((fun a : Fin n →₀ ℕ ↦
            WithLp.toLp 2 (fun j ↦ (a j : ℝ))) ''
              ((G.augmentedSystem W pivot i).support : Set (Fin n →₀ ℕ)))
        isCompact' :=
          (((G.augmentedSystem W pivot i).support.finite_toSet).image
            (fun a ↦ WithLp.toLp 2 (fun j ↦ (a j : ℝ)))).isCompact_convexHull ℝ }
  let partialSum : Finset (Fin n) →
      TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)) := fun J ↦
    { carrier := ∑ i ∈ J, (P i : Set (EuclideanSpace ℝ (Fin n)))
      isCompact' := by
        induction J using Finset.induction_on with
        | empty =>
          change IsCompact ({0} : Set (EuclideanSpace ℝ (Fin n)))
          exact isCompact_singleton
        | @insert i J hi ih =>
          simpa [Finset.sum_insert hi] using (P i).isCompact.add ih }
  ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
    (-1 : ℝ) ^ (n - #J) *
      (MeasureTheory.volume
        (partialSum J : Set (EuclideanSpace ℝ (Fin n)))).toReal

/-- Equatoriality: the mixed volume equals the attained greatest finite count of distinct
positive states, over all positive rates and nonempty classes. -/
def Network.Equatorial {n d : ℕ} (G : Network n)
    (W : Matrix (Fin d) (Fin n) ℝ) (pivot : OrderEmbedding (Fin d) (Fin n)) : Prop :=
  let counts : Set ℕ := {k | ∃ rates : G.reactions → ℝ,
    (∀ e, 0 < rates e) ∧ ∃ c : Fin d → ℝ,
      (∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i) ∧ W.mulVec x = c) ∧
      ({x : Fin n → ℝ | (∀ i, 0 < x i) ∧ W.mulVec x = c ∧
        ∀ i, MvPolynomial.eval x (G.massAction rates i) = 0}.encard = k)}
  ∃ k : ℕ, IsGreatest counts k ∧ G.mixedVolume W pivot = (k : ℝ)

/-- **Conjecture 9** (p. 9). A strongly connected equatorial network remains equatorial after
full reversibilization.

The row-reduced convention is read as RREF in the species order, with the same conservation
matrix; no nondegeneracy or generic-rate condition restricts the positive-state maximum. -/
theorem conjecture_9 {n d : ℕ} (G : Network n)
    (W : Matrix (Fin d) (Fin n) ℝ) (pivot : OrderEmbedding (Fin d) (Fin n))
    (hRREF : W.IsReducedRowEchelon)
    (hrows : LinearIndependent ℝ (fun r ↦ WithLp.toLp 2 (W r)))
    (hspan : Submodule.span ℝ (Set.range fun r ↦ WithLp.toLp 2 (W r)) =
      G.stoichiometric.orthogonal)
    (hpivot : ∀ r, W.IsLeadingEntry r (pivot r))
    (hconnected : ∀ a b : G.complexes,
      Relation.ReflTransGen (fun a b ↦ (a, b) ∈ G.reactions) a b)
    (hequatorial : G.Equatorial W pivot) :
    G.fullyReversible.Equatorial W pivot := by
  sorry

end Sofia2019Efficient
