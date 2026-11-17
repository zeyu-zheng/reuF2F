import Mathlib

/-!
# Bounded ribbonlength for knot families and multi-twist Mobius bands

Authors: Elizabeth Denne and Timi Patterson.
Origin: [Washington and Lee University Summer Research Scholars
2024](https://arxiv.org/abs/2509.18370v2).
Reference: E. Denne and T. Patterson, *Bounded ribbonlength for knot families and multi-twist
Mobius bands*, arXiv:2509.18370v2 (2025).
-/

noncomputable section

namespace Denne2025Bounded

open scoped Real

/-- A fundamental region in the unfolded strip, cut along an oblique transversal of slope `a`. -/
abbrev PaperDomain (l w a : ℝ) (mobius : Bool) :=
  {z : ℂ // a * z.im ≤ z.re ∧
    z.re ≤ l + (if mobius then -a else a) * z.im ∧
    z.im ∈ Set.Icc (-w / 2) (w / 2)}

/-- A folded paper strip, whose flat folded map is encoded by ordered affine cuts and Euclidean
isometries on the intervening panels. The seam may be any fold, and cuts may subdivide an
unfolded panel without a new fold. -/
structure PaperStrip (width : {w : ℝ // 0 < w}) where
  /-- The length of the fundamental region of the strip. -/
  length : ℝ
  length_pos : 0 < length
  /-- Whether the end identification produces a Mobius ribbon. -/
  mobius : Bool
  /-- The slope of the seam cut at which the strip ends are identified. -/
  seamSlope : ℝ
  /-- The total number of panels; one panel lies between each pair of consecutive cuts. -/
  panels : ℕ
  panels_pos : 0 < panels
  /-- The ordered affine cuts, each the line `x = a + b * y` given by `(a, b)`. -/
  cuts : Fin (panels + 1) → ℝ × ℝ
  first_cut : cuts 0 = (0, seamSlope)
  last_cut : cuts (Fin.last panels) = (length, if mobius then -seamSlope else seamSlope)
  ordered_cuts : ∀ i : Fin panels, ∀ y : ℝ,
    y ∈ Set.Icc (-(width : ℝ) / 2) ((width : ℝ) / 2) →
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
def PaperStrip.Seam {width : {w : ℝ // 0 < w}} (R : PaperStrip width)
    (x y : PaperDomain R.length (width : ℝ) R.seamSlope R.mobius) : Prop :=
  x.val.re = R.seamSlope * x.val.im ∧
    y.val.re = R.length + (if R.mobius then -R.seamSlope else R.seamSlope) * y.val.im ∧
    x.val.im = (if R.mobius then -y.val.im else y.val.im)

/-- The topological ribbon surface. -/
abbrev PaperStrip.Surface {width : {w : ℝ // 0 < w}} (R : PaperStrip width) := Quot R.Seam

/-- The continuous folded map on the glued paper surface. -/
def PaperStrip.surfaceMap {width : {w : ℝ // 0 < w}} (R : PaperStrip width) :
    C(R.Surface, ℂ) where
  toFun := Quot.lift R.flatMap
    (fun x y h ↦ R.end_match x y h.1 h.2.1 h.2.2)
  continuous_toFun := continuous_quot_lift _ R.flatMap.continuous

/-- The intrinsic centerline points, parametrized proportionally to paper length. -/
def PaperStrip.corePoint {width : {w : ℝ // 0 < w}} (R : PaperStrip width)
    (t : unitInterval) : R.Surface :=
  Quot.mk R.Seam ⟨⟨R.length * (t : ℝ), 0⟩, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [mul_zero] using mul_nonneg (le_of_lt R.length_pos) t.property.1
    · simp only [mul_zero, add_zero]
      nlinarith [t.property.2, R.length_pos]
    · linarith [width.property]
    · linarith [width.property]⟩

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

/-- The finitely many intrinsic ribbon components of a link, all with a single positive width
(Section 2.1). -/
structure RibbonPaper where
  /-- The common positive width of all ribbon components. -/
  width : {w : ℝ // 0 < w}
  /-- The number of ribbon components. -/
  components : ℕ
  components_pos : 0 < components
  /-- The paper strip of each component. -/
  strip : Fin components → PaperStrip width

/-- The disjoint union of the glued paper surfaces. -/
abbrev RibbonPaper.Surface (R : RibbonPaper) :=
  (i : Fin R.components) × (R.strip i).Surface

/-- The folded map of the whole ribbon link, with the disjoint-union topology. -/
def RibbonPaper.surfaceMap (R : RibbonPaper) : C(R.Surface, ℂ) where
  toFun p := (R.strip p.1).surfaceMap p.2
  continuous_toFun := continuous_sigma (fun i ↦ (R.strip i).surfaceMap.continuous)

/-- The intrinsic link centerline inside the whole paper surface. The seam quotients close each
component's centerline before heights are assigned. -/
abbrev RibbonPaper.Core (R : RibbonPaper) :=
  {x : R.Surface // ∃ t : Fin R.components × unitInterval,
    x = ⟨t.1, (R.strip t.1).corePoint t.2⟩}

/-- An allowed folded ribbon link, with one continuous sheet order on all coincident surface
points. The core height must realize every induced crossing; no framing or regular projection
is fixed. -/
structure FoldedRibbonLink where
  /-- The underlying ribbon components. -/
  paper : RibbonPaper
  /-- The over-under information on all coincident surface points. -/
  crossing : CrossingInformation paper.surfaceMap
  /-- The height function on the intrinsic core giving its spatial lift. -/
  height : C(paper.Core, ℝ)
  height_order : ∀ x y : paper.Core,
    ∀ (hne : x.val ≠ y.val)
      (heq : paper.surfaceMap x.val = paper.surfaceMap y.val),
    crossing.isOver ⟨(x.val, y.val), hne, heq⟩ = true ↔ height y < height x

/-- The spatial core of all components, using the height compatible with the whole-surface
order. -/
def FoldedRibbonLink.spatialCore (R : FoldedRibbonLink) :
    C(R.paper.Core, EuclideanSpace ℝ (Fin 3)) where
  toFun x := WithLp.toLp 2 ![(R.paper.surfaceMap x.val).re,
    (R.paper.surfaceMap x.val).im, R.height x]
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
    exact ((Complex.continuous_re.comp
      (R.paper.surfaceMap.continuous.comp continuous_subtype_val)).finCons
      ((Complex.continuous_im.comp
        (R.paper.surfaceMap.continuous.comp continuous_subtype_val)).finCons
        (R.height.continuous.finCons continuous_const)))

/-- The closed two-strand braid with `q` half-twists on the standard unknotted torus. Both
antipodal strands are present, giving one component for odd `q` and two for even `q`. -/
def torusLink (q : ℤ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  Set.range (fun p : Fin 2 × unitInterval ↦
    let longitude := 2 * π * (p.2 : ℝ)
    let meridian := (q : ℝ) * π * (p.2 : ℝ) + (p.1.val : ℝ) * π
    WithLp.toLp 2
      ![(2 + Real.cos meridian) * Real.cos longitude,
        (2 + Real.cos meridian) * Real.sin longitude, Real.sin meridian])

/-- **Conjecture 23** (p. 19). For every integer `q ≥ 11`, the infimal folded ribbonlength of the
full `(2,q)`-torus link is `8 * √3`.

The ratio uses total core length and a common width, and only the ambient link type is fixed;
even `q` is included, as in the source. -/
theorem conjecture_23 (q : ℤ) (hq : 11 ≤ q) :
    IsGLB {r : ℝ | ∃ R : FoldedRibbonLink,
      (∃ H : unitInterval →
          (EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)),
        Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦ H p.1 p.2) ∧
        Continuous (fun p : unitInterval × EuclideanSpace ℝ (Fin 3) ↦
          (H p.1).symm p.2) ∧
        H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin 3)) ∧
        H 1 '' torusLink q = Set.range R.spatialCore) ∧
      r = (∑ i : Fin R.paper.components, (R.paper.strip i).length) /
        (R.paper.width : ℝ)} (8 * √3) := by
  sorry

end Denne2025Bounded
