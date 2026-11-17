import Mathlib

/-!
# Origamis associated to minimally-intersecting filling pairs

Authors: Tarik Aougab, William W. Menasco, and Mark Nieland.
Origin: [Summer@ICERM 2018](https://icerm.brown.edu/program/summer@icerm/si-18).
Reference: T. Aougab, W. W. Menasco, and M. Nieland, *Origamis associated to
minimally-intersecting filling pairs*, preprint (2022), 15 pp.; arXiv:2108.10268v2.
-/

namespace Aougab2022Origamis

/-- Square-gluing permutations of degree `2g - 1` in the minimal stratum `H(2g - 2)`. Products act
right to left, and connectedness follows from the full commutator cycle. -/
def Origami (g : ℕ) :=
  { p : Equiv.Perm (Fin (2 * g - 1)) × Equiv.Perm (Fin (2 * g - 1)) //
    2 ≤ g ∧ (p.1 * p.2 * p.1⁻¹ * p.2⁻¹).IsCycleOn Set.univ }

instance (g : ℕ) : Finite (Origami g) := by
  unfold Origami
  infer_instance

/-- Relabel every square simultaneously in the horizontal and vertical gluings. -/
def relabel {g : ℕ} (s : Equiv.Perm (Fin (2 * g - 1)))
    (o : Origami g) : Origami g :=
  ⟨(s * o.val.1 * s⁻¹, s * o.val.2 * s⁻¹), o.property.1, by
    have h := o.property.2.conj (g := s)
    have he : (s * o.val.1 * s⁻¹) * (s * o.val.2 * s⁻¹) *
        (s * o.val.1 * s⁻¹)⁻¹ * (s * o.val.2 * s⁻¹)⁻¹ =
        s * (o.val.1 * o.val.2 * o.val.1⁻¹ * o.val.2⁻¹) * s⁻¹ := by
      group
    rw [he]
    simpa only [Set.image_univ, Equiv.range_eq_univ] using h⟩

/-- The standard determinant-one horizontal shear and its inverse on ambient origamis. -/
def shearT (g : ℕ) : Equiv.Perm (Origami g) where
  toFun o := ⟨(o.val.1, o.val.2 * o.val.1⁻¹), o.property.1, by
    convert o.property.2 using 1; group⟩
  invFun o := ⟨(o.val.1, o.val.2 * o.val.1), o.property.1, by
    convert o.property.2 using 1; group⟩
  left_inv o := by
    apply Subtype.ext
    group
  right_inv o := by
    apply Subtype.ext
    group

/-- The standard determinant-one vertical shear and its inverse on ambient origamis. -/
def shearU (g : ℕ) : Equiv.Perm (Origami g) where
  toFun o := ⟨(o.val.1 * o.val.2⁻¹, o.val.2), o.property.1, by
    convert o.property.2 using 1; group⟩
  invFun o := ⟨(o.val.1 * o.val.2, o.val.2), o.property.1, by
    convert o.property.2 using 1; group⟩
  left_inv o := by
    apply Subtype.ext
    group
  right_inv o := by
    apply Subtype.ext
    group

/-- Generating moves for the `SL(2, ℤ)` orbit, including square relabeling. Paths in the
equivalence closure may pass through non-minimal origamis. -/
def OrbitStep {g : ℕ} (o p : Origami g) : Prop :=
  (∃ s : Equiv.Perm (Fin (2 * g - 1)), relabel s o = p) ∨
    shearT g o = p ∨ shearU g o = p

/-- Minimal [1,1] origamis: both gluing permutations are cycles on every square. -/
def MinimalOrigami (g : ℕ) :=
  { o : Origami g // o.val.1.IsCycleOn Set.univ ∧ o.val.2.IsCycleOn Set.univ }

instance (g : ℕ) : Finite (MinimalOrigami g) := by
  unfold MinimalOrigami
  infer_instance

/-- The count `N_g` of orbits containing a minimal `[1,1]` origami (Conjecture 1.2). Orbits are
formed among all origamis before restricting to minimal ones. -/
noncomputable def orbitCount (g : ℕ) : ℕ :=
  let Q := Quotient (Setoid.comap (fun o : MinimalOrigami g ↦ o.val)
    (Relation.EqvGen.setoid (@OrbitStep g)))
  letI : Fintype Q := Fintype.ofFinite Q
  Fintype.card Q

/-- **Conjecture 1.2** (arXiv v2). The orbit counts `N_g` eventually exceed every exponential
in `g`.

The moves are the standard determinant-one shears, not the source's erroneous matrix display. -/
theorem conjecture_1_2 (b : ℝ) (hb : 1 < b) :
    ∃ G ≥ 3,
      ∀ g ≥ G, b ^ g < (orbitCount g : ℝ) := by
  sorry

end Aougab2022Origamis
