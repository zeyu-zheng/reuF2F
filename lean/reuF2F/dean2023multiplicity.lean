import Mathlib

/-!
# Multiplicity-free gonality on graphs

Authors: Frances Dean, Max Everett, and Ralph Morrison.
Origin: [Williams College SMALL REU 2018 and 2020](https://math.williams.edu/small/).
Reference: F. Dean, M. Everett, and R. Morrison, *Multiplicity-free gonality on graphs*,
Electron. J. Graph Theory Appl. **11** (2023), no. 2, 357-380; doi:10.5614/ejgta.2023.11.2.2;
arXiv:2107.12955v1.
-/

noncomputable section

namespace Dean2023Multiplicity

open Finset

open scoped Classical in
/-- Linear equivalence of divisors: their difference lies in the integer column image of the
Laplacian (Section 2).

The Laplacian counts edge occurrences, so parallel edges are retained. -/
def DivisorEquivalent {V E : Type*} {G : Graph V E} [Fintype G.vertexSet] [Fintype G.edgeSet]
    (D D' : G.vertexSet → ℤ) : Prop :=
  ∃ z : G.vertexSet → ℤ,
    D - D' = (Matrix.of fun x y : G.vertexSet ↦
      if x = y then (#{e : G.edgeSet | G.Inc e.val x.val} : ℤ)
      else -(#{e : G.edgeSet | G.IsLink e.val x.val y.val} : ℤ)).mulVec z

/-- The divisorial gonality: the minimum degree of a divisor of positive rank (Section 2).

Positive rank is encoded as every vertex carrying a chip in some effective equivalent divisor. -/
def gonality {V E : Type*} (G : Graph V E) [Fintype G.vertexSet] [Fintype G.edgeSet] : ℤ :=
  sInf {degree : ℤ | ∃ D : G.vertexSet → ℤ,
    (∀ v, ∃ D' : G.vertexSet → ℤ, (∀ w, 0 ≤ D' w) ∧ 1 ≤ D' v ∧ DivisorEquivalent D D') ∧
      ∑ v, D v = degree}

/-- The multiplicity-free gonality: the minimum degree of a positive-rank divisor with every
coefficient `0` or `1` (Section 2). -/
def multiplicityFreeGonality {V E : Type*} (G : Graph V E) [Fintype G.vertexSet]
    [Fintype G.edgeSet] : ℤ :=
  sInf {degree : ℤ | ∃ D : G.vertexSet → ℤ,
    (∀ v, 0 ≤ D v ∧ D v ≤ 1) ∧
      (∀ v, ∃ D' : G.vertexSet → ℤ, (∀ w, 0 ≤ D' w) ∧ 1 ≤ D' v ∧ DivisorEquivalent D D') ∧
      ∑ v, D v = degree}

open scoped Classical in
/-- **Question 5.9** (Section 5.4, arXiv v1 p. 15). Some 3-regular graph has gonality strictly
less than its multiplicity-free gonality.

Graphs are finite connected loopless multigraphs, and 3-regularity counts incident edges rather
than neighbours. -/
theorem question_5_9 :
    ∃ n m : ℕ, ∃ G : Graph (Fin n) (Fin m),
      G.Loopless ∧ G.toSimpleGraph.Connected ∧
        (∀ v : G.vertexSet, #{e : G.edgeSet | G.Inc e.val v.val} = 3) ∧
        gonality G < multiplicityFreeGonality G := by
  sorry

end Dean2023Multiplicity
