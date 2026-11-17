import Mathlib

/-!
# The Tri-Pants Graph of the Twice-Punctured Torus

Authors: Katherine Betts, Troy Larsen, Jeffrey Utley, and Avalon Vanis.
Origin: [University of Virginia REU 2021](https://uva.theopenscholar.com/ken-ono/reus-archive-2021).
Reference: K. Betts, T. Larsen, J. Utley, and A. Vanis, *The tri-pants graph of the
twice-punctured torus*, preprint (2021); arXiv:2111.07136v1.
-/

noncomputable section

namespace Betts2021Tri

open Finset

/-- The marked coordinate torus. -/
abbrev Torus := UnitAddCircle × UnitAddCircle

/-- The torus with two distinct punctures, in fixed coordinates. -/
abbrev Surface := {x : Torus // x ≠ (0, 0) ∧ x ≠ (((1 / 2 : ℝ) : UnitAddCircle), 0)}

/-- Simple nonseparating parametrized circles in the twice-punctured surface. -/
abbrev SimpleCurve := {c : C(UnitAddCircle, Surface) //
  Function.Injective c ∧ IsConnected (Set.range c)ᶜ}

/-- Unoriented free-homotopy classes of simple curves. -/
abbrev Curve := Quotient (Relation.EqvGen.setoid fun r s : SimpleCurve ↦
  ContinuousMap.Homotopic r.val s.val ∨
    ContinuousMap.Homotopic r.val
      (s.val.comp ⟨fun t : UnitAddCircle ↦ -t, continuous_neg⟩))

/-- The minimal geometric intersection over all simple representatives (Definition 1.8).
Infinite intersections have value `⊤`. -/
def intersectionNumber (a b : Curve) : ℕ∞ :=
  sInf {n | ∃ r s : SimpleCurve,
    Quotient.mk _ r = a ∧ Quotient.mk _ s = b ∧
      (Set.range r.val ∩ Set.range s.val).encard = n}

/-- The interior of a pair of pants, a plane with two points deleted. -/
abbrev OpenPants := {x : ℝ × ℝ // x ≠ (0, 0) ∧ x ≠ (1, 0)}

open scoped Classical in
/-- An unordered nonseparating pants decomposition (Definitions 2.3 and 2.5). -/
def IsPantsPair (p : Finset Curve) : Prop :=
  ∃ r s : SimpleCurve,
    (Quotient.mk _ r : Curve) ≠ (Quotient.mk _ s : Curve) ∧
    p = {Quotient.mk _ r, Quotient.mk _ s} ∧
    Disjoint (Set.range r.val) (Set.range s.val) ∧
    Nonempty ({x : Surface // x ∉ Set.range r.val ∧ x ∉ Set.range s.val} ≃ₜ
      (OpenPants ⊕ OpenPants))

open scoped Classical in
/-- A tri-pant: six curve classes partitioned into three pants pairs (Definition 2.10). The
partition is only required to exist; it is not part of the vertex data. -/
abbrev TriPant := {t : Finset Curve // #t = 6 ∧
  ∃ P : Finset (Finset Curve), #P = 3 ∧
    (∀ p ∈ P, IsPantsPair p) ∧ P.biUnion id = t ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q) ∧
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ∀ a ∈ p, ∀ b ∈ q, intersectionNumber a b = 1}

open scoped Classical in
/-- The tri-pants graph, where adjacency means sharing two whole pants pairs
(Definitions 2.11 and 3.9). -/
def triPantsGraph : SimpleGraph TriPant where
  Adj t u := t ≠ u ∧
    #({p ∈ t.val.powerset | IsPantsPair p} ∩
      {p ∈ u.val.powerset | IsPantsPair p}) = 2
  symm.symm := by
    intro t u h
    refine ⟨h.1.symm, ?_⟩
    rw [Finset.inter_comm]
    exact h.2
  loopless.irrefl := by
    intro t h
    exact h.1 rfl

/-- Rational slopes and infinity as primitive integer pairs modulo common sign. -/
structure FareySlope where
  /-- The numerator of the slope. -/
  num : ℤ
  /-- The denominator of the slope, zero for the slope infinity. -/
  den : ℤ
  primitive : num.natAbs.Coprime den.natAbs
  canonical : 0 < den ∨ (den = 0 ∧ num = 1)

/-- A triangle of the full Farey graph of Definition 3.1. -/
abbrev FareyTriangle := {t : Finset FareySlope // #t = 3 ∧
  ∀ v ∈ t, ∀ w ∈ t, v ≠ w → (v.num * w.den - w.num * v.den).natAbs = 1}

open scoped Classical in
/-- The dual Farey graph, with shared-edge adjacency (Definition 3.3). -/
def fareyDual : SimpleGraph FareyTriangle where
  Adj t u := t ≠ u ∧ #(t.val ∩ u.val) = 2
  symm.symm := by
    intro t u h
    refine ⟨h.1.symm, ?_⟩
    rw [Finset.inter_comm]
    exact h.2
  loopless.irrefl := by
    intro t h
    exact h.1 rfl

/-- The slopes of the projection: the set of filled slopes of the six curve classes, so classes
with equal slope contribute one element. Representatives may have either orientation. -/
def slopeImage (t : TriPant) : Set FareySlope :=
  {v | ∃ a ∈ t.val, ∃ r : SimpleCurve, Quotient.mk _ r = a ∧
    ContinuousMap.Homotopic
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(Surface, Torus)).comp r.val)
      (⟨fun t : UnitAddCircle ↦ (v.num • t, v.den • t), by fun_prop⟩ :
        C(UnitAddCircle, Torus))}

/-- **Unnumbered conjecture** (Conclusion, p. 32). Every vertex fiber of the puncture-filling
projection is graph-isomorphic to the dual Farey graph.

Curves are unparametrized and unoriented, although Definition 1.2 omits reversal. A fiber is the
set of tri-pants with a given slope image, with all inherited edges, including the big-flip edges
collapsed by the projection; the isomorphism need not be canonical. -/
theorem fibers_are_farey_dual (v : FareyTriangle) :
    Nonempty ((triPantsGraph.induce {t | slopeImage t = (v.val : Set FareySlope)}) ≃g
      fareyDual) := by
  sorry

end Betts2021Tri
