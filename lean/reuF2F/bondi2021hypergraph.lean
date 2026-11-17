import Mathlib

/-!
# A hypergraph characterization of nearly complete intersections

Authors: Chiara Bondi, Courtney R. Gibbons, Yuye Ke, Spencer Martin,
Shrunal Pothagoni, and Andrew Stelzer.
Origin: [Virtual COURAGE REU 2020](https://arxiv.org/abs/2101.08401v2).
Reference: C. Bondi, C. R. Gibbons, Y. Ke, S. Martin, S. Pothagoni, and A. Stelzer, *A hypergraph
characterization of nearly complete intersections*, preprint (2021), 18 pp.; arXiv:2101.08401v2.
-/

noncomputable section

namespace Bondi2021Hypergraph

open Finset

/-- The squarefree (hyper)edge ideal of a finite family (Definition 2.3). -/
def edgeIdeal (K : Type*) [Field K] {n : ℕ} (E : Finset (Finset (Fin n))) :
    Ideal (MvPolynomial (Fin n) K) :=
  Ideal.span ((fun e : Finset (Fin n) ↦
    (∏ i ∈ e, MvPolynomial.X i : MvPolynomial (Fin n) K)) ''
      (E : Set (Finset (Fin n))))

/-- The substitution `I(x = 1)`, defined on generators by evaluation (p. 2). -/
def setVariableOne {K : Type*} [Field K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (x : Fin n) :
    Ideal (MvPolynomial (Fin n) K) :=
  I.map (MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i ↦ if i = x then 1 else MvPolynomial.X i))

/-- A minimal squarefree generator family defining a nearly complete intersection: not a complete
intersection, but every supported substitution `x = 1` is (p. 2). -/
def IsNearlyCompleteIntersection (K : Type*) [Field K] {n : ℕ}
    (E : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ E, e.Nonempty) ∧
  (∀ e ∈ E, ∀ f ∈ E, e ⊆ f → e = f) ∧
  (¬∃ rs : List (MvPolynomial (Fin n) K),
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K) rs ∧
      Ideal.ofList rs = edgeIdeal K E) ∧
  ∀ x : Fin n, (∃ e ∈ E, x ∈ e) →
    ∃ rs : List (MvPolynomial (Fin n) K),
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K) rs ∧
        Ideal.ofList rs = setVariableOne (edgeIdeal K E) x

/-- **Unnumbered conjecture** (after Theorem 4.6, pp. 14-15). Projective dimension strictly
decreases after setting to one any variable of a removed higher-degree minimal generator.

Both projective dimensions are those of the ideals as modules. -/
theorem strict_projective_dimension
    (K : Type*) [Field K] {n : ℕ} (E : Finset (Finset (Fin n)))
    (hE : IsNearlyCompleteIntersection K E)
    (h : Finset (Fin n)) (hh : h ∈ E) (hdegree : 3 ≤ #h)
    (x : Fin n) (hx : x ∈ h) :
    CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial (Fin n) K) (setVariableOne (edgeIdeal K (E.erase h)) x)) <
      CategoryTheory.projectiveDimension
        (ModuleCat.of (MvPolynomial (Fin n) K) (edgeIdeal K (E.erase h))) := by sorry

end Bondi2021Hypergraph
