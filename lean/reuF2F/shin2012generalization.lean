import Mathlib

/-!
# A Generalization of an Action of the Braid Group on Upper-Triangular Matrices

Author: Minseon Shin.
Origin: [MIT SPUR 2011](https://math.mit.edu/research/undergraduate/spur/past-projects.html).
Reference: M. Shin, *A Generalization of an Action of the Braid Group on Upper-Triangular
Matrices*, Harvard College Math. Rev. **4** (Spring 2012), 4-16.
-/

noncomputable section

namespace Shin2012Generalization

/-- The ring `k[X,Y]`, with one `X` variable for each strict upper-triangular position and `m`
auxiliary `Y` variables (pp. 5 and 8). -/
abbrev SourcePolynomial (n m : ℕ) (K : Type*) [CommRing K] :=
  MvPolynomial ({p : Fin n × Fin n // p.1 < p.2} ⊕ Fin m) K

/-- The polynomial `P_[n]` on the enlarged coefficient-variable ring (Definition 14; before
Lemma 19). -/
def P {n m : ℕ} {K : Type*} [CommRing K]
    (f : Fin n → SourcePolynomial n m K) : SourcePolynomial n m K :=
  (∑ i, f i ^ 2) +
    ∑ p : {p : Fin n × Fin n // p.1 < p.2},
      MvPolynomial.X (Sum.inl p) * f p.val.1 * f p.val.2

/-- The map `T_l`: negate the other coordinates and update coordinate `l` (Definition 16).
The source's `X_jl` for `j ≠ l` uses the unordered-pair index convention. -/
def T {n m : ℕ} {K : Type*} [CommRing K] (l : Fin n)
    (f : Fin n → SourcePolynomial n m K) : Fin n → SourcePolynomial n m K :=
  fun i ↦ if i = l then f l +
    (∑ j : {j : Fin n // j < l},
      MvPolynomial.X (Sum.inl ⟨(j.val, l), j.property⟩) * f j.val) +
    (∑ j : {j : Fin n // l < j},
      MvPolynomial.X (Sum.inl ⟨(l, j.val), j.property⟩) * f j.val)
  else -f i

/-- **Conjecture 20** (p. 8). Every polynomial solution of `P_[n](f) = 1` reduces by a finite
sequence of maps `T_l` to a signed coordinate vector.

Positive dimension, empty auxiliary variables and an empty word use the standard finite
conventions; no matrix-column, degree or rational-coefficient restriction is imposed. -/
theorem conjecture_20 (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    {n m : ℕ} (hn : 0 < n) (f : Fin n → SourcePolynomial n m K)
    (hf : P f = 1) :
    ∃ word : List (Fin n), ∃ j : Fin n,
      word.foldr T f = (fun i ↦ if i = j then 1 else 0) ∨
      word.foldr T f = (fun i ↦ if i = j then -1 else 0) := by sorry

end Shin2012Generalization
