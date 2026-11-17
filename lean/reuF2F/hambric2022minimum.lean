import Mathlib

/-!
# Minimum number of non-zero-entries in a stable matrix exhibiting Turing instability

Authors: Christopher Logan Hambric, Chi-Kwong Li, Diane Christine Pelejo, and Junping Shi.
Origin: [William & Mary EXTREEMS-QED](https://api.nsf.gov/services/v1/awards/1331021.json).
Reference: C. L. Hambric, C.-K. Li, D. C. Pelejo, and J. Shi, *Minimum number of non-zero-entries
in a stable matrix exhibiting Turing instability*, Discrete Contin. Dyn. Syst. Ser. S **15**
(2022), no. 9, 2497–2511; doi:10.3934/dcdss.2021128.
-/

noncomputable section

namespace Hambric2022Minimum

/-- Strict stability of a real matrix, tested on all its complex eigenvalues. -/
def Stable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ, Module.End.HasEigenvalue (Matrix.toLin' (A.map Complex.ofReal)) z → z.re < 0

/-- Irreducibility: strong connectivity of the directed nonzero support on all vertices. -/
def IsIrreducible {n : ℕ} {K : Type*} [Zero K]
    (A : Matrix (Fin n) (Fin n) K) : Prop :=
  letI : Quiver (Fin n) := { Hom := fun i j ↦ PLift (A i j ≠ 0) }
  Quiver.IsStronglyConnected (Fin n)

/-- A sign pattern is potentially stable if it has a stable real realization. -/
def PotentiallyStable {n : ℕ} (S : Matrix (Fin n) (Fin n) SignType) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, SignType.sign (A i j) = S i j) ∧ Stable A

/-- Turing instability: strict stability is lost after subtracting some positive multiple of a
nonnegative diagonal matrix. Zero diffusion coefficients are allowed. -/
def TuringInstability {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Stable A ∧ ∃ P : Matrix (Fin n) (Fin n) ℝ, ∃ t : ℝ,
    P.IsDiag ∧ (∀ i, 0 ≤ P i i) ∧ 0 < t ∧
      ¬Stable (A - t • P)

/-- **Unnumbered conjecture** (following (1), p. 2499). The minimum support size of an
irreducible potentially stable sign pattern is strictly smaller than that of an irreducible matrix
exhibiting Turing instability.

The printed sentence says `n ∈ ℕ`; the model domain `n ≥ 2` is inherited from context. Both minima
are attained, and instability negates the same strict stability predicate, without requiring an
eigenvalue with strictly positive real part. -/
theorem minimum_support_gap (n : ℕ) (hn : 2 ≤ n) :
    ∃ m s : ℕ,
      IsLeast {k : ℕ | ∃ S : Matrix (Fin n) (Fin n) SignType,
        IsIrreducible S ∧ PotentiallyStable S ∧
          {p : Fin n × Fin n | S p.1 p.2 ≠ 0}.ncard = k} m ∧
      IsLeast {k : ℕ | ∃ A : Matrix (Fin n) (Fin n) ℝ,
        IsIrreducible A ∧ TuringInstability A ∧
          {p : Fin n × Fin n | A p.1 p.2 ≠ 0}.ncard = k} s ∧
      m < s := by
  sorry

end Hambric2022Minimum
