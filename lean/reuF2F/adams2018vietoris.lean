import Mathlib

/-!
# Vietoris--Rips Complexes of Regular Polygons

Authors: Henry Adams, Samir Chowdhury, Adam Quinn Jaffe, and Bonginkosi Sibanda.
Origin: [Summer@ICERM 2017](https://icerm.brown.edu/program/summer@icerm/si-17).
Reference: H. Adams, S. Chowdhury, A. Q. Jaffe, and B. Sibanda, *Vietoris--Rips complexes of
regular polygons*, arXiv:1807.10971.
-/

noncomputable section

namespace Adams2018Vietoris

open Set
open scoped Real

/-- The normalized counterclockwise boundary coordinate on `P_n` (Section 2). The interval
`[0, 1)` parametrizes the polygon starting at the vertex `1`. -/
abbrev polygonParameter := Set.Ico (0 : ℝ) 1

/-- The regular polygon's `k`-th vertex, in the Euclidean complex plane. -/
def regularPolygonVertex (n : ℕ) (k : ℤ) : ℂ :=
  ⟨Real.cos (2 * π * (k : ℝ) / (n : ℝ)),
    Real.sin (2 * π * (k : ℝ) / (n : ℝ))⟩

/-- The parametrization of the polygon by fractional edge count, extended periodically
(Section 2). -/
def polygonPoint (n : ℕ) (t : ℝ) : ℂ :=
  let u := (n : ℝ) * Int.fract t
  (1 - Int.fract u) • regularPolygonVertex n ⌊u⌋ +
    Int.fract u • regularPolygonVertex n (⌊u⌋ + 1)

/-- An equilateral `(2l + 1)`-star inscribed in the polygon (Section 4.2). The winding number
`l` is encoded as the sum of counterclockwise advances, each less than half the perimeter. -/
structure InscribedStar (n l : ℕ) (t : polygonParameter) where
  /-- The parameters of the star's `2l + 1` vertices on the polygon. -/
  vertex : Fin (2 * l + 1) → polygonParameter
  base : vertex 0 = t
  distinct : Function.Injective vertex
  /-- The common side length of the star. -/
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_cyclic : scale ≤ if Even n then 2 * Real.cos (π / n)
    else 1 + Real.cos (2 * π / n) / Real.cos (π / n)
  equal_sides : ∀ i : Fin (2 * l + 1),
    dist (polygonPoint n (vertex i).1) (polygonPoint n (vertex (i + 1)).1) = scale
  counterclockwise : ∀ i : Fin (2 * l + 1),
    Int.fract ((vertex (i + 1)).1 - (vertex i).1) < 1 / 2
  winding : (∑ i : Fin (2 * l + 1),
    Int.fract ((vertex (i + 1)).1 - (vertex i).1)) = (l : ℝ)

/-- The star side-length function `s_(2l+1)` (Definition 4.13, Section 5.2). The scale set is a
singleton on the conjecture domain; outside it the infimum is a junk value. -/
def starSideLength (n l : ℕ) (t : polygonParameter) : ℝ :=
  sInf {r : ℝ | ∃ S : InscribedStar n l t, S.scale = r}

/-- A vertex crossing: the inscribed star contains a polygon vertex (Section 5.2). -/
def IsVertexCrossing (n l : ℕ) (t : polygonParameter) : Prop :=
  ∃ S : InscribedStar n l t, ∃ i : Fin (2 * l + 1), ∃ k : Fin n,
    polygonPoint n (S.vertex i).1 = regularPolygonVertex n k.1

/-- A midpoint crossing: the star contains a polygon edge midpoint (Section 5.2). -/
def IsMidpointCrossing (n l : ℕ) (t : polygonParameter) : Prop :=
  ∃ S : InscribedStar n l t, ∃ i : Fin (2 * l + 1), ∃ k : Fin n,
    polygonPoint n (S.vertex i).1 =
      (1 / 2 : ℝ) • (regularPolygonVertex n k.1 + regularPolygonVertex n (k.1 + 1))

/-- **Conjecture 5.10** (arXiv:1807.10971v1, p. 15). Midpoint and vertex crossings are
alternating global minima and maxima of the star side length, which is strictly monotone on each
intervening counterclockwise arc.

The model uses the source's p. 13 endpoint extension: for `n = 4 * l + 2`, vertex-based stars
have scale `r_n`, since Lemma 5.5's strict-radius exception is erroneous. -/
theorem conjecture_5_10_star_side_length_extrema (n l : ℕ)
    (hl : 1 ≤ l) (hn : 4 * l + 2 ≤ n) :
    let pointAt : ℝ → polygonParameter := fun t ↦
      ⟨Int.fract t, Int.fract_nonneg t, Int.fract_lt_one t⟩
    (∀ t : polygonParameter, IsMidpointCrossing n l t →
      ∀ u : polygonParameter, starSideLength n l t ≤ starSideLength n l u) ∧
    (∀ t : polygonParameter, IsVertexCrossing n l t →
      ∀ u : polygonParameter, starSideLength n l u ≤ starSideLength n l t) ∧
    (∀ t : polygonParameter,
      IsMidpointCrossing n l t ∨ IsVertexCrossing n l t →
      ∃ δ > (0 : ℝ), δ < 1 ∧
        (∀ ε > (0 : ℝ), ε < δ →
          ¬(IsMidpointCrossing n l (pointAt (t.1 + ε)) ∨
            IsVertexCrossing n l (pointAt (t.1 + ε)))) ∧
        ((IsMidpointCrossing n l t ∧
            IsVertexCrossing n l (pointAt (t.1 + δ)) ∧
            StrictMonoOn (fun ε ↦ starSideLength n l (pointAt (t.1 + ε)))
              (Set.Icc 0 δ)) ∨
          (IsVertexCrossing n l t ∧
            IsMidpointCrossing n l (pointAt (t.1 + δ)) ∧
            StrictAntiOn (fun ε ↦ starSideLength n l (pointAt (t.1 + ε)))
              (Set.Icc 0 δ)))) := by
  sorry

end Adams2018Vietoris
