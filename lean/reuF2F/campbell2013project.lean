import Mathlib

/-!
# Project on Logic and Operator Algebras

Authors: John Campbell, Jonathan Herman, Thomas Hu, Boris Kadets, Vlad Kalashnyk,
Meghan Miholics, Jiewon Park, Paul Sacawa, and Nigel Sequeira.
Origin: [Fields Undergraduate Summer Research Program
2013](https://www.fields.utoronto.ca/programs/scientific/13-14/summer-research13/mini-conf.html).
Reference: J. Campbell, J. Herman, T. Hu, B. Kadets, V. Kalashnyk, M. Miholics, J. Park,
P. Sacawa, and N. Sequeira, *Project on logic and operator algebras*, Fields Undergraduate
Summer Research Program final report (2013), 17 pp.
-/

noncomputable section

namespace Campbell2013Project

open scoped NNReal

/-- The AF property of a separable unital C*-algebra: an increasing sequence of
finite-dimensional unital *-subalgebras with norm-dense union. -/
@[nolint unusedArguments]
def IsAF (A : Type*) [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] : Prop :=
  ∃ stages : ℕ → StarSubalgebra ℂ A,
    Monotone stages ∧
    (∀ n, FiniteDimensional ℂ (stages n)) ∧
    Dense (⋃ n, (stages n : Set A))

section ProjectionSetup

variable {A : Type*} [CStarAlgebra A]

/-- Finite matrix representatives of projections in the stabilization. -/
structure FiniteProjection (A : Type*) [CStarAlgebra A] where
  /-- The matrix size of the representative. -/
  size : ℕ
  /-- The projection matrix with entries in `A`. -/
  value : CStarMatrix (Fin size) (Fin size) A
  isProjection : IsStarProjection value

/-- Murray-von Neumann equivalence by partial-isometry equations at one finite size (p. 8). -/
def MurrayVonNeumann {n : ℕ}
    (p q : CStarMatrix (Fin n) (Fin n) A) : Prop :=
  ∃ v : CStarMatrix (Fin n) (Fin n) A, star v * v = p ∧ v * star v = q

/-- Block-diagonal addition of projection representatives (p. 9). -/
def projectionBlockSum (p q : FiniteProjection A) : FiniteProjection A where
  size := p.size + q.size
  value := CStarMatrix.reindexₐ ℂ A finSumFinEquiv
    (CStarMatrix.ofMatrix
      (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.value) 0 0
        (CStarMatrix.ofMatrix.symm q.value)))
  isProjection := by
    apply IsStarProjection.map _ (CStarMatrix.reindexₐ ℂ A finSumFinEquiv)
    apply IsStarProjection.map _ CStarMatrix.ofMatrixStarAlgEquiv
    have hp : IsStarProjection (CStarMatrix.ofMatrix.symm p.value) :=
      p.isProjection.map CStarMatrix.ofMatrixStarAlgEquiv.symm
    have hq : IsStarProjection (CStarMatrix.ofMatrix.symm q.value) :=
      q.isProjection.map CStarMatrix.ofMatrixStarAlgEquiv.symm
    have hp2 : (CStarMatrix.ofMatrix.symm p.value) *
        (CStarMatrix.ofMatrix.symm p.value) = CStarMatrix.ofMatrix.symm p.value :=
      hp.isIdempotentElem.eq
    have hq2 : (CStarMatrix.ofMatrix.symm q.value) *
        (CStarMatrix.ofMatrix.symm q.value) = CStarMatrix.ofMatrix.symm q.value :=
      hq.isIdempotentElem.eq
    have hps : Matrix.conjTranspose (CStarMatrix.ofMatrix.symm p.value) =
        CStarMatrix.ofMatrix.symm p.value := hp.isSelfAdjoint.star_eq
    have hqs : Matrix.conjTranspose (CStarMatrix.ofMatrix.symm q.value) =
        CStarMatrix.ofMatrix.symm q.value := hq.isSelfAdjoint.star_eq
    constructor
    · change Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.value) 0 0
          (CStarMatrix.ofMatrix.symm q.value) *
          Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.value) 0 0
          (CStarMatrix.ofMatrix.symm q.value) = _
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        hp2, hq2]
    · change (Matrix.fromBlocks (CStarMatrix.ofMatrix.symm p.value) 0 0
          (CStarMatrix.ofMatrix.symm q.value)).conjTranspose = _
      rw [Matrix.fromBlocks_conjTranspose]
      simp only [Matrix.conjTranspose_zero, hps, hqs]

/-- Stabilization by adding a zero block (p. 8). -/
def projectionPad (p : FiniteProjection A) (k : ℕ) : FiniteProjection A :=
  projectionBlockSum p ⟨k, 0, IsStarProjection.zero _⟩

/-- Stable equivalence: pad both projections with zero blocks to a common size and compare by a
partial isometry. -/
def StableMurrayVonNeumann (p q : FiniteProjection A) : Prop :=
  ∃ (k l : ℕ) (h : p.size + k = q.size + l),
    MurrayVonNeumann
      (CStarMatrix.reindexₐ ℂ A (finCongr h) (projectionPad p k).value)
      (projectionPad q l).value

/-- The defining relations of the Grothendieck group: stable equivalence, block-sum addition and
the zero projection. -/
def k0Relations (A : Type*) [CStarAlgebra A] :
    AddSubgroup (FreeAbelianGroup (FiniteProjection A)) :=
  AddSubgroup.closure {x |
    (∃ p q, StableMurrayVonNeumann p q ∧
      x = FreeAbelianGroup.of p - FreeAbelianGroup.of q) ∨
    (∃ p q, x = FreeAbelianGroup.of (projectionBlockSum p q) -
      FreeAbelianGroup.of p - FreeAbelianGroup.of q) ∨
    x = FreeAbelianGroup.of (⟨0, 0, IsStarProjection.zero _⟩ : FiniteProjection A)}

/-- The group `K₀`, presented by finite projections modulo these relations. -/
abbrev K0 (A : Type*) [CStarAlgebra A] :=
  FreeAbelianGroup (FiniteProjection A) ⧸ k0Relations A

/-- The class of a projection in `K₀`. -/
def projectionClass (p : FiniteProjection A) : K0 A :=
  QuotientAddGroup.mk' (k0Relations A) (FreeAbelianGroup.of p)

/-- The positive cone: the image of all projection classes. -/
def k0Positive (A : Type*) [CStarAlgebra A] : Set (K0 A) :=
  Set.range (projectionClass (A := A))

/-- The distinguished class of the `1 × 1` identity projection. -/
def k0Unit (A : Type*) [CStarAlgebra A] : K0 A :=
  projectionClass ⟨1, 1, IsStarProjection.one _⟩

end ProjectionSetup

/-- Function symbols of the ordered `K₀` structure: zero, the identity class, negation and
addition. -/
inductive K0Function : ℕ → Type
  | zero : K0Function 0
  | unit : K0Function 0
  | neg : K0Function 1
  | add : K0Function 2

/-- The unary positive-cone predicate of the ordered `K₀` structure. -/
inductive K0Relation : ℕ → Type
  | positive : K0Relation 1

/-- The first-order language of ordered groups with a distinguished identity class. -/
def k0Language : FirstOrder.Language := ⟨K0Function, K0Relation⟩

/-- The interpretation of the language in `K₀` by its group, positive cone and identity class. -/
@[instance_reducible]
def k0Language.structure (G : Type*) [AddCommGroup G] (cone : Set G) (unit : G) :
    k0Language.Structure G where
  funMap
    | .zero, _ => 0
    | .unit, _ => unit
    | .neg, v => -v 0
    | .add, v => v 0 + v 1
  RelMap
    | .positive, v => v 0 ∈ cone

/-- The ball sort: the closed ball of radius `r + 1`, so every positive integer radius occurs. -/
abbrev ball (A : Type*) [CStarAlgebra A] (r : ℕ) :=
  Metric.closedBall (0 : A) ((r : ℝ) + 1)

/-- An assignment of the finitely many free variables to their declared ball sorts. -/
abbrev Valuation (A : Type*) [CStarAlgebra A] {n : ℕ} (r : Fin n → ℕ) :=
  (i : Fin n) → ball A (r i)

/-- Continuous formulas: norms of noncommutative *-polynomials, continuous nonnegative
connectives and ball-sorted quantifiers. In atoms `(i, true)` is `x_i*`; quantifiers bind index
zero and shift the free variables. -/
inductive Formula : ℕ → Type
  | norm {n : ℕ} (p : FreeAlgebra ℂ (Fin n × Bool)) : Formula n
  | connective {n : ℕ} (k : ℕ)
      (f : C((Fin k → ℝ≥0), ℝ≥0)) (args : Fin k → Formula n) : Formula n
  | infimum {n : ℕ} (r : ℕ) (body : Formula (n + 1)) : Formula n
  | supremum {n : ℕ} (r : ℕ) (body : Formula (n + 1)) : Formula n

/-- The value of a formula. The returned bound makes quantifier suprema finite, so no junk value
of an unbounded supremum arises. -/
def Formula.eval {n : ℕ} (φ : Formula n) :
    ∀ (A : Type*) [CStarAlgebra A] (r : Fin n → ℕ),
    {f : Valuation A r → ℝ≥0 // BddAbove (Set.range f)} :=
  match φ with
  | .norm p => fun A _ r ↦
    let interp (v : Valuation A r) :=
      FreeAlgebra.lift ℂ (fun i : Fin n × Bool ↦
        if i.2 then star (v i.1).val else (v i.1).val)
    have hb : ∀ p : FreeAlgebra ℂ (Fin n × Bool),
        BddAbove (Set.range (fun v : Valuation A r ↦ ‖interp v p‖₊)) := by
      intro p
      induction p using FreeAlgebra.induction with
      | grade0 c =>
        refine ⟨‖algebraMap ℂ A c‖₊, ?_⟩
        rintro y ⟨v, rfl⟩
        simp only [interp, AlgHom.commutes, le_refl]
      | add p q hp hq =>
        rcases hp with ⟨cp, hcp⟩
        rcases hq with ⟨cq, hcq⟩
        refine ⟨cp + cq, ?_⟩
        rintro y ⟨v, rfl⟩
        simp only [map_add]
        exact (nnnorm_add_le (interp v p) (interp v q)).trans
          (add_le_add (hcp (Set.mem_range_self v)) (hcq (Set.mem_range_self v)))
      | mul p q hp hq =>
        rcases hp with ⟨cp, hcp⟩
        rcases hq with ⟨cq, hcq⟩
        refine ⟨cp * cq, ?_⟩
        rintro y ⟨v, rfl⟩
        simp only [map_mul]
        exact (nnnorm_mul_le (interp v p) (interp v q)).trans
          (mul_le_mul' (hcp (Set.mem_range_self v)) (hcq (Set.mem_range_self v)))
      | grade1 i =>
        refine ⟨(r i.1 : ℝ≥0) + 1, ?_⟩
        rintro y ⟨v, rfl⟩
        have hv : ‖(v i.1).val‖ ≤ (r i.1 : ℝ) + 1 := by
          simpa only [ball, Metric.mem_closedBall, dist_zero_right] using (v i.1).property
        have hn : ‖(v i.1).val‖₊ ≤ (r i.1 : ℝ≥0) + 1 := hv
        simpa only [interp, FreeAlgebra.lift_ι_apply, apply_ite, nnnorm_star,
          ite_self] using hn
    ⟨fun v ↦ ‖interp v p‖₊, hb p⟩
  | .connective k f args => fun A _ r ↦
    let fs := fun i ↦ (args i).eval A r
    ⟨fun v ↦ f (fun i ↦ (fs i).val v), by
      choose c hc using fun i ↦ (fs i).property
      apply ((isCompact_Icc : IsCompact (Set.Icc (0 : Fin k → ℝ≥0) c)).image
        f.continuous).bddAbove.mono
      rintro y ⟨v, rfl⟩
      exact ⟨fun i ↦ (fs i).val v,
        ⟨fun i ↦ bot_le, fun i ↦ hc i (Set.mem_range_self v)⟩, rfl⟩⟩
  | .infimum s body => fun A _ r ↦
    let fs := body.eval A (Fin.cons s r)
    let extend (v : Valuation A r) (a : ball A s) : Valuation A (Fin.cons s r) :=
      Fin.cases a v
    let z : ball A s := ⟨0, by simp only [ball, Metric.mem_closedBall, dist_self]; positivity⟩
    letI : Nonempty (ball A s) := ⟨z⟩
    ⟨fun v ↦ ⨅ a : ball A s, fs.val (extend v a), by
      rcases fs.property with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rintro y ⟨v, rfl⟩
      exact (ciInf_le (OrderBot.bddBelow _) z).trans (hc (Set.mem_range_self _))⟩
  | .supremum s body => fun A _ r ↦
    let fs := body.eval A (Fin.cons s r)
    let extend (v : Valuation A r) (a : ball A s) : Valuation A (Fin.cons s r) :=
      Fin.cases a v
    let z : ball A s := ⟨0, by simp only [ball, Metric.mem_closedBall, dist_self]; positivity⟩
    letI : Nonempty (ball A s) := ⟨z⟩
    ⟨fun v ↦ ⨆ a : ball A s, fs.val (extend v a), by
      rcases fs.property with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rintro y ⟨v, rfl⟩
      exact ciSup_le (fun a ↦ hc (Set.mem_range_self _))⟩

/-- The value of a sentence. -/
def Formula.sentenceValue (σ : Formula 0) (A : Type*) [CStarAlgebra A] : ℝ≥0 :=
  (σ.eval A Fin.elim0).val (fun i ↦ Fin.elim0 i)

/-- The continuous theory: the sentences with value zero. -/
def continuousTheory (A : Type*) [CStarAlgebra A] : Set (Formula 0) :=
  {σ | σ.sentenceValue A = 0}

/-- **The Crazy Conjecture** (Section 2.3, p. 12). For separable unital AF C*-algebras, elementary
equivalence of the ordered `K₀` groups with identity classes implies continuous elementary
equivalence. -/
theorem crazy_conjecture (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]
    [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B]
    (hA : IsAF A) (hB : IsAF B) :
    letI := k0Language.structure (K0 A) (k0Positive A) (k0Unit A)
    letI := k0Language.structure (K0 B) (k0Positive B) (k0Unit B)
    FirstOrder.Language.ElementarilyEquivalent k0Language (K0 A) (K0 B) →
      continuousTheory A = continuousTheory B := by
  sorry

end Campbell2013Project
