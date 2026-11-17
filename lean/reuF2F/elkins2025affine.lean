import Mathlib

/-!
# Affine standard Lyndon words

Authors: Corbet Elkins and Alexander Tsymbaliuk.
Origin: [Purdue University REU 2025](https://www.math.purdue.edu/~otsymbal/Papers/AffineSL.pdf).
Reference: C. Elkins and A. Tsymbaliuk, *Affine standard Lyndon words*, preprint (2025);
arXiv:2505.15432.
-/

noncomputable section

namespace Elkins2025Affine

open Finset

/-- A nonempty word smaller than every nonempty proper suffix (Definition 2.3). -/
def IsLyndon {A : Type*} [LinearOrder A] (w : List A) : Prop :=
  w ≠ [] ∧ ∀ n > 0, n < w.length → w < w.drop n

open scoped Classical in
/-- The cut of the costandard factorization: the longest proper Lyndon suffix. -/
def costandardCut {A : Type*} [LinearOrder A] (w : List A) : ℕ :=
  let cuts := {n ∈ Finset.range w.length | 0 < n ∧ IsLyndon (w.drop n)}
  if h : cuts.Nonempty then cuts.min' h else 0

open scoped Classical in
/-- The standard prefix, namely the longest proper Lyndon prefix (Proposition 2.7). -/
def standardPrefix {A : Type*} [LinearOrder A] (w : List A) : List A :=
  w.take (({n ∈ Finset.range w.length | IsLyndon (w.take n)}).sup id)

/-- The remaining suffix of the standard factorization (Proposition 2.7). -/
def standardSuffix {A : Type*} [LinearOrder A] (w : List A) : List A :=
  w.drop (standardPrefix w).length

/-- Standard bracketing by the costandard factorization (Definition 2.11). Values lie in
Mathlib's Serre construction `Matrix.ToLieAlgebra`; only the empty word gets the junk value 0. -/
def standardBracket {A : Type*} [LinearOrder A] (a : Matrix A A ℤ)
    (w : List A) : Matrix.ToLieAlgebra ℂ a :=
  if h : w.length = 1 then
    LieSubmodule.Quotient.mk
      (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E (w[0]'(by omega))))
  else
    let n := costandardCut w
    if hcut : 0 < n ∧ n < w.length then
      ⁅standardBracket a (w.take n), standardBracket a (w.drop n)⁆
    else 0
termination_by w.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- Standard Lyndon words: the bracket is outside the span of larger Lyndon
brackets in the reverse-length/lexicographic order (Definition 2.14). -/
def IsStandardLyndon {A : Type*} [LinearOrder A] (a : Matrix A A ℤ)
    (w : List A) : Prop :=
  IsLyndon w ∧ standardBracket a w ∉ Submodule.span ℂ
    {x | ∃ v : List A, IsLyndon v ∧
      (v.length < w.length ∨ (v.length = w.length ∧ w < v)) ∧
      x = standardBracket a v}

open scoped Classical in
/-- The standard Lyndon words of a degree in decreasing lexicographic order (Section 2.24).
Indices are zero-based, and indices outside the list return the empty word. -/
def standardWord {A : Type*} [Fintype A] [LinearOrder A]
    (a : Matrix A A ℤ) (d : A → ℕ) (i : ℕ) : List A :=
  let words := (Finset.univ : Finset (Fin (∑ j, d j) → A)).image List.ofFn
  let selected := {w ∈ words | (∀ j, w.count j = d j) ∧ IsStandardLyndon a w}
  (selected.sort (fun u v ↦ v ≤ u)).getD i []

section RootSystem

variable {R V W : Type*} [Fintype R]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {P : RootPairing R ℝ V W} [P.IsCrystallographic] (b : P.Base)

/-- The untwisted affine Cartan matrix (Section 2.22). The extra letter `none` represents
minus the highest finite root. -/
def affineCartan (θ : R) : Matrix (Option b.support) (Option b.support) ℤ
  | none, none => 2
  | none, some j => -P.pairingIn ℤ j θ
  | some i, none => -P.pairingIn ℤ θ i
  | some i, some j => P.pairingIn ℤ j i

/-- The coefficients of the minimal imaginary root `δ = α₀ + θ`. -/
def imaginaryRoot (θ : R) : Option b.support → ℕ
  | none => 1
  | some j => (b.toWeightBasisInt.repr (P.rootSpanMem ℤ θ) j).toNat

omit [Fintype R] in
/-- **Conjecture 6.27** (arXiv; Conjecture 6.26 in the June 19, 2025 author revision). Every
imaginary standard Lyndon word and its standard prefix repeat a fixed cyclic rotation of an
earlier degree-`δ` word.

All untwisted types, alphabet orders, indices and positive multiples are retained, not merely
eventual periodicity. -/
theorem conjecture_6_27 [Finite R] [Nonempty R] [P.IsRootSystem] [P.IsReduced] [P.IsIrreducible]
    (θ : R) (hθ : ∀ β : R, b.height β ≤ b.height θ)
    [LinearOrder (Option b.support)] (i : Fin #b.support) :
    let δ := imaginaryRoot b θ
    let a := affineCartan b θ
    let u := standardWord a δ i.val
    ∃ j : ℕ, j ≤ i.val ∧ ∃ w : List (Option b.support),
      List.IsRotated w (standardWord a δ j) ∧
      ∀ k > 0,
        let v := standardWord a (fun x ↦ k * δ x) i.val
        v = standardPrefix u ++
            (List.replicate (k - 1) w).flatten ++
              standardSuffix u ∧
        standardPrefix v = standardPrefix u ++
          (List.replicate (k - 1) w).flatten := by
  sorry

end RootSystem

end Elkins2025Affine
