import Mathlib

/-!
# l-adic properties of partition functions

Authors: Eva Belmont, Holden Lee, Alexandra Musat, and Sarah Trebat-Leder.
Origin: [Emory University REU in Number Theory
2011](https://uva.theopenscholar.com/ken-ono/reus-archive-2011).
Reference: E. Belmont, H. Lee, A. Musat, and S. Trebat-Leder, *l-adic properties of partition
functions*, Monatsh. Math. **173** (2014), no. 1, 1-34; arXiv:1510.01202v1.
-/

noncomputable section

namespace Belmont2015L

/-- Coefficientwise reduction of a rational `q`-series modulo `ell`. It is used only for
`ell`-integral series; other denominators give junk values. -/
def reduction (ell : ℕ) [Fact ell.Prime] (a : PowerSeries ℚ) : PowerSeries (ZMod ell) :=
  PowerSeries.mk fun n ↦ ((a.coeff n).num : ZMod ell) / ((a.coeff n).den : ZMod ell)

/-- The reductions modulo `ell` of the `ell`-integral level-one forms in `M_k`. -/
def modularFormsMod (ell : ℕ) [Fact ell.Prime] (k : ℤ) : Set (PowerSeries (ZMod ell)) :=
  {g | ∃ (f : ModularForm (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range k)
      (a : PowerSeries ℚ),
    (∀ n, ¬ell ∣ (a.coeff n).den) ∧
    a.map (Rat.castHom ℂ) = UpperHalfPlane.qExpansion 1 f ∧
    reduction ell a = g}

/-- The reductions modulo `ell` of the `ell`-integral level-one cusp forms in `S_k`. -/
def cuspFormsMod (ell : ℕ) [Fact ell.Prime] (k : ℤ) : Set (PowerSeries (ZMod ell)) :=
  {g | ∃ (f : CuspForm (Matrix.SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range k)
      (a : PowerSeries ℚ),
    (∀ n, ¬ell ∣ (a.coeff n).den) ∧
    a.map (Rat.castHom ℂ) = UpperHalfPlane.qExpansion 1 f ∧
    reduction ell a = g}

/-- The formal `q`-series of `η(ell ^ 2 z) / η(z)` reduced modulo `ell` (equation (2.2)). The
Euler products are pentagonal series, and only primes `ell ≥ 5` are intended. -/
def phi (ell : ℕ) [Fact ell.Prime] : PowerSeries (ZMod ell) :=
  let E := PowerSeries.pentagonalSeries (ZMod ell)
  let hE : PowerSeries.constantCoeff E = (1 : (ZMod ell)) := by
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply, pentagonal, E] using
      (PowerSeries.coeff_pentagonalSeries_pentagonal (ZMod ell) (0 : ℤ))
  let e : Units (PowerSeries (ZMod ell)) :=
    { val := E
      inv := PowerSeries.invOfUnit E 1
      val_inv := PowerSeries.mul_invOfUnit E 1 hE
      inv_val := PowerSeries.invOfUnit_mul E 1 hE }
  PowerSeries.X ^ ((ell ^ 2 - 1) / 24) *
    PowerSeries.expand (ell ^ 2) (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)) E *
    ((e ^ (-1 : ℤ) : Units (PowerSeries (ZMod ell))) : PowerSeries (ZMod ell))

/-- Atkin's `U` operator, extracting coefficients at multiples of `ell` (equation (2.1)). -/
def U (ell : ℕ) (g : PowerSeries (ZMod ell)) : PowerSeries (ZMod ell) :=
  PowerSeries.mk fun n ↦ g.coeff (ell * n)

/-- The operator `D_r`: multiply by `Φ_ell ^ r`, then apply `U(ell)` (equation (2.3)). -/
def D (ell r : ℕ) [Fact ell.Prime] (g : PowerSeries (ZMod ell)) :
    PowerSeries (ZMod ell) :=
  U ell (g * phi ell ^ r)

/-- The operator `X_r`: `U` followed by `D_r`, in the source's right-action notation
(equation (2.4)). -/
def X (ell r : ℕ) [Fact ell.Prime] (g : PowerSeries (ZMod ell)) :
    PowerSeries (ZMod ell) :=
  D ell r (U ell g)

/-- The odd invertible part: all subspaces of the reduced odd cusp space on which `X_r` is
bijective (Section 4, (5.2)). It uses odd-`X`/even-`Y`, correcting the reversed names printed
before (5.2). -/
def oddStableSpace (ell r : ℕ) [Fact ell.Prime] :
    Submodule (ZMod ell) (PowerSeries (ZMod ell)) :=
  sSup {W | (W : Set (PowerSeries (ZMod ell))) ⊆
      cuspFormsMod ell (((r / 2 + 1) * (ell - 1) : ℕ) : ℤ) ∧
    Set.BijOn (X ell r) (W : Set (PowerSeries (ZMod ell))) W}

/-- **Unnumbered conjecture** (after (5.3)). The operator `D_r` sends every reduced
`ell`-integral form in `M_(ell-1)` into the odd `X_r`-invertible part.

This is the equivalent `t = 0` form; the printed odd/even operator names are read as
odd-`X`/even-`Y`. -/
theorem conjecture_after_5_3 (r : ℕ) {ell : ℕ} [Fact ell.Prime]
    (hr : 1 ≤ r) (hell : r + 5 ≤ ell) (g : PowerSeries (ZMod ell))
    (hg : g ∈ modularFormsMod ell ((ell - 1 : ℕ) : ℤ)) :
    D ell r g ∈ (oddStableSpace ell r : Set (PowerSeries (ZMod ell))) := by
  sorry

end Belmont2015L
