import Mathlib

/-!
# The d-gonal locus in the moduli space of tropical plane curves

Authors: Desmond Leitz, Ralph Morrison, Soren Newman-Taylor, and Vincent X. Wang.
Origin: [Williams College SMALL REU 2025](https://math.williams.edu/small/research-publications/).
Reference: D. Leitz, R. Morrison, S. Newman-Taylor, and V. X. Wang, *The d-gonal locus in the
moduli space of tropical plane curves*, arXiv:2511.20805v1 (2025), 43 pp.
-/

noncomputable section

namespace Leitz2025D

open WithLp
open Finset

/-- A two-variable min-tropical Laurent polynomial with finite support (Section 2.4). -/
abbrev TropicalPolynomial := AddMonoidAlgebra (MinTropical (WithTop ℝ)) (Fin 2 → ℤ)

/-- The Newton polygon, the convex hull of the finite exponents (Section 2.4). -/
def newtonPolygon (f : TropicalPolynomial) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ ((fun a : Fin 2 → ℤ ↦ toLp 2 fun i ↦ (a i : ℝ)) ''
    (f.coeff.support : Set (Fin 2 → ℤ)))

/-- The exponents on the lower face exposed by a point of the tropical plane (Section 2.4). -/
def lowerFace (f : TropicalPolynomial) (x : EuclideanSpace ℝ (Fin 2)) : Finset (Fin 2 → ℤ) :=
  let h := fun a ↦ (MinTropical.untrop (f.coeff a)).untopD 0
  {a ∈ f.coeff.support | ∀ b ∈ f.coeff.support,
    h a + ∑ i, (a i : ℝ) * x i ≤ h b + ∑ i, (b i : ℝ) * x i}

/-- The tropical curve, the locus where at least two monomials minimize (Section 2.4). -/
def tropicalCurve (f : TropicalPolynomial) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | 2 ≤ #(lowerFace f x)}

/-- Smoothness: complete lattice support and a unimodular lower triangulation (Section 2.4). -/
def IsSmooth (f : TropicalPolynomial) : Prop :=
  (interior (newtonPolygon f)).Nonempty ∧
    (∀ a : Fin 2 → ℤ, toLp 2 (fun i ↦ (a i : ℝ)) ∈ newtonPolygon f →
      a ∈ f.coeff.support) ∧
    ∀ x : EuclideanSpace ℝ (Fin 2),
      #(lowerFace f x) ≤ 3 ∧
      (#(lowerFace f x) = 3 → ∃ a b c : Fin 2 → ℤ,
        lowerFace f x = {a, b, c} ∧
        |(b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)| = 1)

/-- The convex hull of the interior lattice points (Section 2.1). -/
def interiorPolygon (P : Set (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {x | ∃ a : Fin 2 → ℤ,
    x = toLp 2 (fun i ↦ (a i : ℝ)) ∧ x ∈ interior P}

/-- The lattice width, measured by primitive integral covectors (Section 2.1). -/
def latticeWidth (P : Set (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  sInf {k : ℕ | ∃ (u : Fin 2 → ℤ) (c : ℤ), Int.gcd (u 0) (u 1) = 1 ∧
    ∀ x ∈ P, (c : ℝ) ≤ ∑ i, (u i : ℝ) * x i ∧
      (∑ i, (u i : ℝ) * x i) ≤ (c : ℝ) + k}

open scoped Classical in
/-- The expected gonality, including the exceptional triangle `2 Upsilon` (Section 2.2). -/
def expectedGonality (P : Set (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  let Q := interiorPolygon P
  if Q = ∅ then 1 else if interior Q = ∅ then 2 else
    if ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (b : Fin 2 → ℤ),
      IsUnit A.det ∧
      P = (fun x : EuclideanSpace ℝ (Fin 2) ↦
        toLp 2 fun i ↦ (∑ j, (A i j : ℝ) * x j) + (b i : ℝ)) ''
          convexHull ℝ ({toLp 2 ![-2, -2], toLp 2 ![2, 0], toLp 2 ![0, 2]} :
            Set (EuclideanSpace ℝ (Fin 2)))
    then 3 else latticeWidth Q + 2

/-- The outgoing edge germs, parametrized at primitive lattice speed (Section 2.3; Morrison,
Tropical geometry, Definition 5). -/
def outgoingDirections (Γ : Set (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : Set (Fin 2 → ℤ) :=
  {v | Int.gcd (v 0) (v 1) = 1 ∧ ∃ ε > (0 : ℝ),
    ∀ t ∈ Set.Ioo 0 ε, p + t • toLp 2 (fun i ↦ (v i : ℝ)) ∈ Γ}

/-- The divisor of a continuous function with local integral slopes along every incident edge
germ (Section 2.3; Gathmann-Kerber, Definition 1.4). -/
def IsPrincipalDivisor (Γ : Set (EuclideanSpace ℝ (Fin 2)))
    (D : EuclideanSpace ℝ (Fin 2) →₀ ℤ) : Prop :=
  (D.support : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Γ ∧
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ, ContinuousOn f Γ ∧
      ∀ p ∈ Γ, ∃ s : (Fin 2 → ℤ) →₀ ℤ,
        (s.support : Set (Fin 2 → ℤ)) ⊆ outgoingDirections Γ p ∧
        (∀ v ∈ outgoingDirections Γ p, ∃ ε > (0 : ℝ),
          ∀ t ∈ Set.Ioo 0 ε,
            f (p + t • toLp 2 (fun i ↦ (v i : ℝ))) = f p + t * (s v : ℝ)) ∧
        D p = s.sum (fun _ z ↦ z)

/-- The least degree of an effective positive-rank divisor on the entire metric graph
(Section 2.3). Principal divisors use lattice lengths, not vertex-only chip-firing. -/
def divisorialGonality (Γ : Set (EuclideanSpace ℝ (Fin 2))) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ d : ℕ, n = (d : ℕ∞) ∧
    ∃ D : EuclideanSpace ℝ (Fin 2) →₀ ℤ,
      (D.support : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Γ ∧
      (∀ p, 0 ≤ D p) ∧ D.sum (fun _ z ↦ z) = (d : ℤ) ∧
      ∀ p ∈ Γ, ∃ D' : EuclideanSpace ℝ (Fin 2) →₀ ℤ,
        (D'.support : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Γ ∧
        (∀ q, 0 ≤ D' q) ∧ IsPrincipalDivisor Γ (D - Finsupp.single p 1 - D')}

/-- **Conjecture 1.1**. Every smooth tropical plane curve has divisorial gonality equal to the
expected gonality of its Newton polygon.

Gonality is taken on a compact truncation retaining all finite vertices, which has the same
gonality as the skeleton, also in genus zero and one. -/
theorem conjecture_1_1 (f : TropicalPolynomial) (hf : IsSmooth f) :
    divisorialGonality (tropicalCurve f ∩ Metric.closedBall 0
        (1 + sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin 2),
          #(lowerFace f x) = 3 ∧ r = ‖x‖} : ℝ)) =
      (expectedGonality (newtonPolygon f) : ℕ∞) := by
  sorry

end Leitz2025D
