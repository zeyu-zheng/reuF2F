import Mathlib

/-!
# Iterated Differential Polynomial Rings over Locally Nilpotent Rings

Authors: Steven Jin and Jooyoung Shin.
Origin: [Kent State University REU
2020](https://www.kent.edu/math/research-experiences-undergraduates).
Reference: S. Jin and J. Shin, *Iterated Differential Polynomial Rings over Locally
Nilpotent Rings*, Comm. Algebra **49** (2021), 256-262; arXiv:2007.07446v2.
-/

noncomputable section

namespace Jin2021Iterated

universe u

/-- A derivation of a possibly nonunital associative ring: an additive map satisfying the Leibniz
rule (p. 1). -/
structure RingDerivation (A : Type u) [NonUnitalRing A] extends A →+ A where
  /-- The Leibniz rule. -/
  leibniz' (a b : A) : toAddMonoidHom (a * b) =
    toAddMonoidHom a * b + a * toAddMonoidHom b

instance {A : Type u} [NonUnitalRing A] : CoeFun (RingDerivation A) (fun _ ↦ A → A) :=
  ⟨fun d ↦ d.toAddMonoidHom⟩

variable {A : Type u} [NonUnitalRing A]

/-- The extension of a derivation to the integer unitization, vanishing on the integers. -/
def RingDerivation.unitized (d : RingDerivation A) :
    Unitization ℤ A →+ Unitization ℤ A where
  toFun x := Unitization.inr (d x.snd)
  map_zero' := by simp [map_zero]
  map_add' x y := by
    change Unitization.inr (d.toAddMonoidHom (x.snd + y.snd)) = _
    simp only [map_add, Unitization.inr_add]

/-- The extension of a derivation to the unitization satisfies the Leibniz rule. -/
lemma RingDerivation.unitized_leibniz (d : RingDerivation A)
    (x y : Unitization ℤ A) :
    d.unitized (x * y) = d.unitized x * y + x * d.unitized y := by
  apply Unitization.ext
  · change (0 : ℤ) = 0 * y.fst + x.fst * 0
    simp
  · change d.toAddMonoidHom (x.fst • y.snd + y.fst • x.snd + x.snd * y.snd) =
      ((0 : ℤ) • y.snd + y.fst • d.toAddMonoidHom x.snd +
        d.toAddMonoidHom x.snd * y.snd) +
      (x.fst • d.toAddMonoidHom y.snd + (0 : ℤ) • x.snd +
        x.snd * d.toAddMonoidHom y.snd)
    simp only [map_add, map_zsmul, d.leibniz', zero_smul, zero_add, add_zero]
    abel

/-- Left multiplication by a coefficient on finite polynomials over the unitization. -/
def coefficient : A →+ AddMonoid.End (ℕ →₀ Unitization ℤ A) where
  toFun a := Finsupp.mapRange.addMonoidHom
    (AddMonoidHom.mulLeft (a : Unitization ℤ A))
  map_zero' := by
    apply AddMonoidHom.ext
    intro p
    apply Finsupp.ext
    intro n
    change (↑(0 : A) : Unitization ℤ A) * p n = 0
    simp
  map_add' a b := by
    apply AddMonoidHom.ext
    intro p
    apply Finsupp.ext
    intro n
    change (↑(a + b) : Unitization ℤ A) * p n =
      (a : Unitization ℤ A) * p n + (b : Unitization ℤ A) * p n
    rw [Unitization.inr_add, add_mul]

/-- The action of the formal variable: index shift plus coefficientwise derivation.

This auxiliary operator need not belong to the nonunital extension. -/
def variableOperator (d : RingDerivation A) :
    AddMonoid.End (ℕ →₀ Unitization ℤ A) :=
  Finsupp.embDomain.addMonoidHom ⟨Nat.succ, Nat.succ_injective⟩ +
    Finsupp.mapRange.addMonoidHom d.unitized

/-- The commutation law `x * a = a * x + d a` of the formal variable with a coefficient. -/
lemma variableOperator_coefficient (d : RingDerivation A) (a : A) :
    variableOperator d * coefficient a =
      coefficient a * variableOperator d + coefficient (d a) := by
  have hc (a : A) (n : ℕ) (b : Unitization ℤ A) :
      coefficient a (Finsupp.single n b) =
        Finsupp.single n ((a : Unitization ℤ A) * b) := by
    change Finsupp.mapRange (AddMonoidHom.mulLeft (a : Unitization ℤ A))
      (map_zero _) (Finsupp.single n b) = _
    exact Finsupp.mapRange_single
  have hx (n : ℕ) (a : Unitization ℤ A) :
      variableOperator d (Finsupp.single n a) =
        Finsupp.single (n + 1) a + Finsupp.single n (d.unitized a) := by
    change Finsupp.embDomain ⟨Nat.succ, Nat.succ_injective⟩ (Finsupp.single n a) +
      Finsupp.mapRange d.unitized d.unitized.map_zero (Finsupp.single n a) = _
    simp
  apply AddMonoidHom.ext
  intro p
  change variableOperator d (coefficient a p) =
    coefficient a (variableOperator d p) + coefficient (d a) p
  induction p using Finsupp.induction with
  | zero => simp
  | @single_add n b p hn hb ih =>
    have hu : d.unitized (a : Unitization ℤ A) = (d a : Unitization ℤ A) := rfl
    have hs : variableOperator d (coefficient a (Finsupp.single n b)) =
        coefficient a (variableOperator d (Finsupp.single n b)) +
          coefficient (d a) (Finsupp.single n b) := by
      simp only [hc, hx, map_add,
        d.unitized_leibniz, hu, Finsupp.single_add]
      abel
    simp only [map_add]
    rw [ih, hs]
    abel

/-- The operator of a finite polynomial with left coefficients. -/
def normalForm (d : RingDerivation A) :
    (ℕ →₀ A) →+ AddMonoid.End (ℕ →₀ Unitization ℤ A) :=
  Finsupp.liftAddHom (fun n ↦
    (AddMonoidHom.mulRight (variableOperator d ^ n)).comp coefficient)

/-- The action of the formal variable on coefficient polynomials, without adjoining an identity. -/
def shiftDerivative (d : RingDerivation A) : AddMonoid.End (ℕ →₀ A) :=
  Finsupp.embDomain.addMonoidHom ⟨Nat.succ, Nat.succ_injective⟩ +
    Finsupp.mapRange.addMonoidHom d.toAddMonoidHom

/-- `normalForm` turns `shiftDerivative` into left multiplication by `variableOperator`. -/
lemma normalForm_shiftDerivative (d : RingDerivation A) (p : ℕ →₀ A) :
    normalForm d (shiftDerivative d p) = variableOperator d * normalForm d p := by
  have hm (n : ℕ) (a : A) : normalForm d (Finsupp.single n a) =
      coefficient a * variableOperator d ^ n := by
    simp [normalForm]
  have hd (n : ℕ) (a : A) : shiftDerivative d (Finsupp.single n a) =
      Finsupp.single (n + 1) a + Finsupp.single n (d a) := by
    change Finsupp.embDomain ⟨Nat.succ, Nat.succ_injective⟩ (Finsupp.single n a) +
      Finsupp.mapRange d.toAddMonoidHom d.toAddMonoidHom.map_zero
        (Finsupp.single n a) = _
    simp
  induction p using Finsupp.induction with
  | zero => simp
  | @single_add n a p hn ha ih =>
    have hs : normalForm d (shiftDerivative d (Finsupp.single n a)) =
        variableOperator d * normalForm d (Finsupp.single n a) := by
      rw [hd, map_add, hm, hm, hm]
      rw [← mul_assoc, variableOperator_coefficient, Distrib.right_distrib, mul_assoc,
        ← pow_succ']
    rw [map_add, map_add, hs, ih, map_add, Distrib.left_distrib]

/-- `coefficient` is multiplicative. -/
lemma coefficient_mul (a b : A) : coefficient (a * b) = coefficient a * coefficient b := by
  apply AddMonoidHom.ext
  intro p
  apply Finsupp.ext
  intro n
  change ((a * b : A) : Unitization ℤ A) * p n =
    (a : Unitization ℤ A) * ((b : Unitization ℤ A) * p n)
  rw [Unitization.inr_mul]
  exact mul_assoc (a : Unitization ℤ A) (b : Unitization ℤ A) (p n)

/-- `normalForm` turns left coefficient multiplication into left multiplication by `coefficient`.
-/
lemma normalForm_left_coefficient (d : RingDerivation A) (a : A) (p : ℕ →₀ A) :
    normalForm d (Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulLeft a) p) =
      coefficient a * normalForm d p := by
  have hm (n : ℕ) (b : A) : normalForm d (Finsupp.single n b) =
      coefficient b * variableOperator d ^ n := by
    simp [normalForm]
  induction p using Finsupp.induction with
  | zero => simp
  | @single_add n b p hn hb ih =>
    have hs : normalForm d
        (Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulLeft a) (Finsupp.single n b)) =
        coefficient a * normalForm d (Finsupp.single n b) := by
      change normalForm d (Finsupp.mapRange (AddMonoidHom.mulLeft a)
        (map_zero _) (Finsupp.single n b)) = _
      rw [Finsupp.mapRange_single, hm, hm]
      exact (congrArg (fun c ↦ c * variableOperator d ^ n) (coefficient_mul a b)).trans
        (mul_assoc _ _ _)
    rw [map_add, map_add, hs, ih, map_add, Distrib.left_distrib]

/-- The product of finite coefficient polynomials, by repeated commutation. -/
def oreMul (d : RingDerivation A) (p q : ℕ →₀ A) : ℕ →₀ A :=
  p.sum fun n a ↦ Finsupp.mapRange.addMonoidHom (AddMonoidHom.mulLeft a)
    ((shiftDerivative d ^ n) q)

/-- `normalForm` is multiplicative for `oreMul`. -/
lemma normalForm_oreMul (d : RingDerivation A) (p q : ℕ →₀ A) :
    normalForm d (oreMul d p q) = normalForm d p * normalForm d q := by
  have hi (n : ℕ) : normalForm d ((shiftDerivative d ^ n) q) =
      variableOperator d ^ n * normalForm d q := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ']
      change normalForm d (shiftDerivative d ((shiftDerivative d ^ n) q)) = _
      rw [normalForm_shiftDerivative, ih, ← mul_assoc, ← pow_succ']
  simp only [oreMul, Finsupp.sum, map_sum, normalForm_left_coefficient, hi]
  change (∑ n ∈ p.support, coefficient (p n) *
      (variableOperator d ^ n * normalForm d q)) = _
  rw [show normalForm d p =
    ∑ n ∈ p.support, coefficient (p n) * variableOperator d ^ n from rfl]
  calc
    _ = ∑ n ∈ p.support, (coefficient (p n) * variableOperator d ^ n) *
        normalForm d q := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (mul_assoc _ _ _).symm
    _ = _ := (Finset.sum_mul p.support
      (fun n ↦ coefficient (p n) * variableOperator d ^ n) (normalForm d q)).symm

/-- The differential polynomial ring `A[X; d]`, realized as the image of `normalForm` (p. 1).

Multiplication is composition of the faithful operators. -/
def differentialExtension (d : RingDerivation A) :
    NonUnitalSubring (AddMonoid.End (ℕ →₀ Unitization ℤ A)) where
  carrier := Set.range (normalForm d)
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, map_add _ _ _⟩
  neg_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨-p, map_neg _ _⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨oreMul d p q, normalForm_oreMul d p q⟩

/-- An iterated differential polynomial ring of length `n` over `A` (Definition 3).

Each derivation is defined on the whole preceding extension. -/
def DifferentialTower : (n : ℕ) → (A : Type u) → [NonUnitalRing A] → Type u
  | 0, _, _ => PUnit
  | n + 1, A, _ => Σ d : RingDerivation A, DifferentialTower n (differentialExtension d)

/-- The last ring of an iterated differential polynomial tower. -/
def DifferentialTower.terminal : {n : ℕ} → {A : Type u} → [NonUnitalRing A] →
    DifferentialTower n A → Type u
  | 0, A, _, _ => A
  | _ + 1, _, _, t => DifferentialTower.terminal t.2

/-- The ring structure of the last ring of a tower. -/
instance DifferentialTower.terminalRing : {n : ℕ} → {A : Type u} → [NonUnitalRing A] →
    (t : DifferentialTower n A) → NonUnitalRing t.terminal
  | 0, _, inst, _ => inst
  | _ + 1, _, _, t => DifferentialTower.terminalRing t.2

/-- **Question 5** (Section 1, arXiv v2 p. 3). Every iterated differential polynomial ring over a
locally nilpotent ring is Behrens radical.

Towers have positive length; local nilpotence means that every finitely generated subring is
nilpotent, and Behrens radicality is encoded as every quotient by a ring congruence having no
nonzero idempotent. -/
theorem question_5 (R : Type u) [NonUnitalRing R]
    (hR : ∀ F : Finset R, ∃ k > 0,
      ∀ w : FreeSemigroup (NonUnitalSubring.closure (F : Set R)),
        w.length = k → FreeSemigroup.lift (fun a ↦ (a : R)) w = 0)
    (n : ℕ) (t : DifferentialTower (n + 1) R) (c : RingCon t.terminal) (a : t.terminal)
    (ha : c (a * a) a) :
    c a 0 := by
  sorry

end Jin2021Iterated
