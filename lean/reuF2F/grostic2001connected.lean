import Mathlib

/-!
# Connected Sums and Decompositions of Plane Curves

Author: Christian J. Grostic.
Origin: [Oregon State University REU
2000](https://sites.science.oregonstate.edu/math_reu/proceedings/2000.html).
Reference: C. J. Grostic, *Connected Sums and Decompositions of Plane Curves*, Oregon State REU
Proceedings, manuscript dated January 26, 2001, pp. 53–74.
-/

noncomputable section

namespace Grostic2001Connected

/-- Generic smooth immersions of the circle in the plane, including embeddings (p. 54). The plane
is encoded as `ℂ`, with regularity and transversality taken over `ℝ`. -/
structure GenericCurve where
  /-- The smooth immersion of the circle into the plane. -/
  curve : ContMDiffMap
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
    (modelWithCornersSelf ℝ ℂ) Circle ℂ ((⊤ : ENat) : WithTop ENat)
  regular : ∀ x : Circle,
    Function.Injective
      (mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) curve x)
  at_most_double : ∀ a b c : Circle,
    curve a = curve b → curve a = curve c → a = b ∨ a = c ∨ b = c
  transverse : ∀ a b : Circle, a ≠ b → curve a = curve b →
    ∀ v : ℂ,
      ∃ u : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) a,
        ∃ w : TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) b,
          mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) curve a u +
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) curve b w = v
  finite_crossings :
    {z : ℂ | ∃ a b : Circle, a ≠ b ∧ curve a = z ∧ curve b = z}.Finite

/-- Equivalence of curves under smooth plane and circle reparametrizations, including orientation
reversals (p. 54). -/
def curveSetoid : Setoid GenericCurve where
  r a b := ∃ F : Diffeomorph
      (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      ℂ ℂ ((⊤ : ENat) : WithTop ENat),
    ∃ h : Diffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      Circle Circle ((⊤ : ENat) : WithTop ENat),
      ∀ t : Circle, F (a.curve t) = b.curve (h t)
  iseqv := {
    refl := by
      intro a
      refine ⟨Diffeomorph.refl (modelWithCornersSelf ℝ ℂ) ℂ _,
        Diffeomorph.refl (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle _, ?_⟩
      intro t
      rfl
    symm := by
      intro a b hab
      obtain ⟨F, h, heq⟩ := hab
      refine ⟨F.symm, h.symm, ?_⟩
      intro t
      have hx := congrArg F.symm (heq (h.symm t))
      simpa only [Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply] using hx.symm
    trans := by
      intro a b c hab hbc
      obtain ⟨F, h, heq⟩ := hab
      obtain ⟨G, k, keq⟩ := hbc
      refine ⟨F.trans G, h.trans k, ?_⟩
      intro t
      change G (F (a.curve t)) = c.curve (k (h t))
      rw [heq t, keq (h t)] }

/-- The multivalued exterior connected sum (Definition 1). A marked disk records the deleted caps
and inserted arcs, and four itineraries record the seams, without an assumed surgery law. -/
def ConnectedSum (left right result : GenericCurve) : Prop :=
  ∃ u : Fin 2 → GenericCurve, ∃ w : GenericCurve,
    curveSetoid.r left (u 0) ∧ curveSetoid.r right (u 1) ∧
    curveSetoid.r w result ∧
    (∀ t : Circle, ((u 0).curve t).re < 0 ∧ 0 < ((u 1).curve t).re) ∧
    ∃ ε > (0 : ℝ),
    ∃ cap retained : Fin 2 → ℝ → Circle,
    ∃ bridge : Fin 2 → ℝ → ℂ,
    ∃ disk : (Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1) → ℂ,
    ∃ itinerary : Fin 4 → ℝ → Circle,
      let I : Set ℝ := Set.Icc 0 1
      let J : Set ℝ := Set.Ioo (-ε) (1 + ε)
      let A : Fin 2 → ℝ → ℂ := fun i t ↦ (u i).curve (cap i t)
      let R : Fin 2 → ℝ → ℂ := fun i t ↦ (u i).curve (retained i t)
      let Z : Set ℂ := Set.range (u 0).curve ∪ Set.range (u 1).curve
      (∀ i : Fin 2,
        ContMDiffOn (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          ((⊤ : ENat) : WithTop ENat) (cap i) J ∧
        ContMDiffOn (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          ((⊤ : ENat) : WithTop ENat) (retained i) J ∧
        Set.InjOn (cap i) I ∧ Set.InjOn (retained i) I ∧
        (∀ t ∈ I,
          Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) (cap i) t) ∧
          Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) (retained i) t)) ∧
        cap i 0 = retained i 1 ∧ cap i 1 = retained i 0 ∧
        (cap i '' I) ∪ (retained i '' I) = Set.univ ∧
        (cap i '' I) ∩ (retained i '' I) = {cap i 0, cap i 1} ∧
        Set.InjOn (A i) I ∧ (u i).curve ⁻¹' (A i '' I) = cap i '' I) ∧
      (∀ i : Fin 2,
        ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ)
          ((⊤ : ENat) : WithTop ENat) (bridge i) J ∧
        ∀ t ∈ I,
          Function.Injective (mvfderiv (modelWithCornersSelf ℝ ℝ) (bridge i) t)) ∧
      Topology.IsEmbedding disk ∧
      (∀ t : Set.Icc (0 : ℝ) 1,
        disk (⟨0, by constructor <;> norm_num⟩, t) = A 0 t ∧
        disk (⟨1, by constructor <;> norm_num⟩, t) = A 1 (1 - (t : ℝ))) ∧
      (∀ s : Set.Icc (0 : ℝ) 1,
        disk (s, ⟨0, by constructor <;> norm_num⟩) = bridge 0 s ∧
        disk (s, ⟨1, by constructor <;> norm_num⟩) = bridge 1 (1 - (s : ℝ))) ∧
      Set.range disk ∩ Z = (A 0 '' I) ∪ (A 1 '' I) ∧
      (∃ z ∈ Zᶜ,
        ¬Bornology.IsBounded (connectedComponentIn Zᶜ z) ∧
        ∀ q : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1,
          (q.1 : ℝ) ≠ 0 → (q.1 : ℝ) ≠ 1 →
          disk q ∈ connectedComponentIn Zᶜ z) ∧
      (∀ k : Fin 4,
        ContMDiffOn (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
          ((⊤ : ENat) : WithTop ENat) (itinerary k) J ∧
        Set.InjOn (itinerary k) I ∧
        (∀ t ∈ I,
          Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) (itinerary k) t)) ∧
        itinerary k 1 = itinerary (k + 1) 0) ∧
      Function.Injective (fun k : Fin 4 ↦ itinerary k 0) ∧
      (⋃ k : Fin 4, itinerary k '' I) = Set.univ ∧
      (∀ k l : Fin 4, k ≠ l →
        (itinerary k '' I) ∩ (itinerary l '' I) =
          if l = k + 1 then {itinerary k 1}
          else if k = l + 1 then {itinerary k 0}
          else ∅) ∧
      (∀ t ∈ I,
        w.curve (itinerary 0 t) = R 0 t ∧
        w.curve (itinerary 1 t) = bridge 0 t ∧
        w.curve (itinerary 2 t) = R 1 t ∧
        w.curve (itinerary 3 t) = bridge 1 t)

/-- Nontrivial prime curves, where both factors of a nontrivial decomposition have double points
(Definition 3). -/
def IsPrimeCurve (g : GenericCurve) : Prop :=
  ¬Function.Injective g.curve ∧
    ¬∃ a b : GenericCurve,
      ¬Function.Injective a.curve ∧ ¬Function.Injective b.curve ∧ ConnectedSum a b g

/-- Finite prime decompositions with all bracketings and class multiplicities (Definition 2 and
Section 7). A crossing-free circle has the empty profile. -/
inductive CompletedDecomposition : GenericCurve → BinaryTree GenericCurve →
    Multiset (Quotient curveSetoid) → Prop
  | unit (g : GenericCurve) (embedded : Function.Injective g.curve) :
      CompletedDecomposition g BinaryTree.nil 0
  | prime (g : GenericCurve) (hprime : IsPrimeCurve g) :
      CompletedDecomposition g (BinaryTree.node g BinaryTree.nil BinaryTree.nil)
        {Quotient.mk curveSetoid g}
  | sum (g a b : GenericCurve) (ha : ¬Function.Injective a.curve)
      (hb : ¬Function.Injective b.curve) (joined : ConnectedSum a b g)
      (ta tb : BinaryTree GenericCurve) (pa pb : Multiset (Quotient curveSetoid))
      (da : CompletedDecomposition a ta pa) (db : CompletedDecomposition b tb pb) :
      CompletedDecomposition g (BinaryTree.node g ta tb) (pa + pb)

/-- **Unnumbered conjecture** (Section 7). Every generic plane curve, not only a tree-like one, has
a finite prime decomposition, and its multiset of prime classes is unique.

Proper factors are read in the nontrivial sense of Definition 6, and the crossing-free circle's
empty profile is a normalization convention not literal in Definitions 3–5. -/
theorem unique_prime_decomposition (g : GenericCurve) :
    (∃ t : BinaryTree GenericCurve, ∃ p : Multiset (Quotient curveSetoid),
      CompletedDecomposition g t p) ∧
    (∀ t₁ t₂ : BinaryTree GenericCurve,
      ∀ p₁ p₂ : Multiset (Quotient curveSetoid),
        CompletedDecomposition g t₁ p₁ → CompletedDecomposition g t₂ p₂ →
          p₁ = p₂) := by
  sorry

end Grostic2001Connected
