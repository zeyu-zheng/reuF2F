import Mathlib

/-!
# Ribbonlength upper bounds for small crossing knots and links

Authors: Zhicheng (Henry) Chen, Elizabeth Denne, Kyle Patterson, and Timi Patterson.
Origin: [Washington and Lee University Summer Research Scholars
2024](https://arxiv.org/abs/2510.16190).
Reference: Z. Chen, E. Denne, K. Patterson, and T. Patterson, *Ribbonlength upper bounds for
small crossing knots and links*, preprint (2025); arXiv:2510.16190v1.
-/

noncomputable section

namespace Chen2025Ribbonlength

/-- A fundamental region of length `l` and width `w` in the unfolded strip, cut along oblique
transversals of slope `a`. -/
abbrev PaperDomain (l w a : ℝ) (mobius : Bool) :=
  {z : ℂ // a * z.im ≤ z.re ∧
    z.re ≤ l + (if mobius then -a else a) * z.im ∧
    z.im ∈ Set.Icc (-w / 2) (w / 2)}

/-- A folded paper strip: ordered affine cuts and Euclidean isometries on the intervening panels
encoding its flat folded map. The seam may be any fold, and cuts may subdivide a panel without
creating a new fold. -/
structure PaperStrip where
  /-- The length of the fundamental region of the strip. -/
  length : ℝ
  /-- The width of the strip. -/
  width : ℝ
  length_pos : 0 < length
  width_pos : 0 < width
  /-- Whether the end identification produces a Mobius ribbon. -/
  mobius : Bool
  /-- The slope of the seam cut at which the strip ends are identified. -/
  seamSlope : ℝ
  /-- The number of panels; consecutive cuts bound one panel. -/
  panels : ℕ
  panels_pos : 0 < panels
  /-- The ordered affine cuts, each the line `x = a + b * y` given by `(a, b)`. -/
  cuts : Fin (panels + 1) → ℝ × ℝ
  first_cut : cuts 0 = (0, seamSlope)
  last_cut : cuts (Fin.last panels) = (length, if mobius then -seamSlope else seamSlope)
  ordered_cuts : ∀ i : Fin panels, ∀ y : ℝ,
    y ∈ Set.Icc (-width / 2) (width / 2) →
    (cuts i.castSucc).1 + (cuts i.castSucc).2 * y <
      (cuts i.succ).1 + (cuts i.succ).2 * y
  /-- The Euclidean isometry by which each panel is placed in the plane. -/
  panel : Fin panels → (ℂ ≃ᵃⁱ[ℝ] ℂ)
  /-- The flat folded map of the fundamental region into the plane. -/
  flatMap : C(PaperDomain length width seamSlope mobius, ℂ)
  on_panel : ∀ i : Fin panels, ∀ z : PaperDomain length width seamSlope mobius,
    (cuts i.castSucc).1 + (cuts i.castSucc).2 * z.val.im ≤ z.val.re →
    z.val.re ≤ (cuts i.succ).1 + (cuts i.succ).2 * z.val.im →
    flatMap z = panel i z.val
  end_match : ∀ x y : PaperDomain length width seamSlope mobius,
    x.val.re = seamSlope * x.val.im →
    y.val.re = length + (if mobius then -seamSlope else seamSlope) * y.val.im →
    x.val.im = (if mobius then -y.val.im else y.val.im) → flatMap x = flatMap y

/-- The end gluing of the intrinsic annulus or Mobius strip. -/
def PaperStrip.Seam (R : PaperStrip)
    (x y : PaperDomain R.length R.width R.seamSlope R.mobius) : Prop :=
  x.val.re = R.seamSlope * x.val.im ∧
    y.val.re = R.length + (if R.mobius then -R.seamSlope else R.seamSlope) * y.val.im ∧
    x.val.im = (if R.mobius then -y.val.im else y.val.im)

/-- The topological ribbon surface. -/
abbrev PaperStrip.Surface (R : PaperStrip) := Quot R.Seam

/-- The continuous folded map on the glued paper surface. -/
def PaperStrip.surfaceMap (R : PaperStrip) : C(R.Surface, ℂ) where
  toFun := Quot.lift R.flatMap
    (fun x y h ↦ R.end_match x y h.1 h.2.1 h.2.2)
  continuous_toFun := continuous_quot_lift _ R.flatMap.continuous

/-- Intrinsic centerline points, parametrized proportionally to paper length. -/
def PaperStrip.corePoint (R : PaperStrip) (t : unitInterval) : R.Surface :=
  Quot.mk R.Seam ⟨⟨R.length * (t : ℝ), 0⟩, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [mul_zero] using mul_nonneg (le_of_lt R.length_pos) t.property.1
    · simp only [mul_zero, add_zero]
      nlinarith [t.property.2, R.length_pos]
    · linarith [R.width_pos]
    · linarith [R.width_pos]⟩

/-- Continuous, antisymmetric, transitive over-under information on distinct coincident points
(Denne--Kamp--Terry--Zhu, Definition 2.2). `true` means the first sheet is above the second. -/
structure CrossingInformation {X : Type} [TopologicalSpace X] (f : X → ℂ) where
  /-- Whether the first of two distinct coincident points lies above the second. -/
  isOver : {p : X × X // p.1 ≠ p.2 ∧ f p.1 = f p.2} → Bool
  continuous_isOver : Continuous isOver
  reversed : ∀ p,
    isOver ⟨(p.val.2, p.val.1), Ne.symm p.property.1, p.property.2.symm⟩ = !(isOver p)
  transitive : ∀ x y z (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (fxy : f x = f y) (fyz : f y = f z),
    isOver ⟨(x, y), hxy, fxy⟩ = true → isOver ⟨(y, z), hyz, fyz⟩ = true →
    isOver ⟨(x, z), hxz, fxy.trans fyz⟩ = true

/-- An allowed folded ribbon with continuous sheet order on its surface and a compatible closed
spatial lift of its core. Regular crossings, framing, stick number and orientability are not
fixed. -/
structure FoldedRibbon where
  /-- The underlying folded paper strip. -/
  strip : PaperStrip
  /-- The over-under information of the folded strip. -/
  crossing : CrossingInformation strip.surfaceMap
  /-- The height function along the core giving its closed spatial lift. -/
  height : C(unitInterval, ℝ)
  height_closed : height 0 = height 1
  height_order : ∀ s t : unitInterval,
    ∀ (hne : strip.corePoint s ≠ strip.corePoint t)
      (heq : strip.surfaceMap (strip.corePoint s) =
        strip.surfaceMap (strip.corePoint t)),
    crossing.isOver ⟨(strip.corePoint s, strip.corePoint t), hne, heq⟩ = true ↔
      height t < height s

/-- The spatial knot of a ribbon: the lift of its folded core by the height function, which is
compatible with the crossing information. -/
def FoldedRibbon.realization (R : FoldedRibbon) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range (fun t : unitInterval ↦ WithLp.toLp 2
    ![(R.strip.surfaceMap (R.strip.corePoint t)).re,
      (R.strip.surfaceMap (R.strip.corePoint t)).im, R.height t])

/-- The figure-eight knot `T_2`, in its standard trigonometric realization. -/
def figureEightKnot : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range (fun t : ℝ ↦ WithLp.toLp 2
    ![(2 + Real.cos (2 * t)) * Real.cos (3 * t),
      (2 + Real.cos (2 * t)) * Real.sin (3 * t), Real.sin (4 * t)])

/-- **Conjecture 12**. The infimal folded ribbonlength of the figure-eight knot, over all allowed
folded ribbons of this knot type, is eight.

The infimum is stated as a greatest lower bound; no minimizing ribbon or fixed framing is
assumed. -/
theorem conjecture_12 :
    IsGLB {r : ℝ | ∃ R : FoldedRibbon,
      (∃ H : unitInterval →
          (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
        Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ H p.1 p.2) ∧
        Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
          (H p.1).symm p.2) ∧
        H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin 3)) ∧
        H 1 '' figureEightKnot = R.realization) ∧ r = R.strip.length / R.strip.width} 8 := by
  sorry

end Chen2025Ribbonlength
