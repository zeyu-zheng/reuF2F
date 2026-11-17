import Mathlib

/-!
# Arborescences of covering graphs

Authors: Sunita Chepuri, CJ Dowd, Andrew Hardt, Gregory Michel,
Sylvester W. Zhang, and Valerie Zhang.
Origin: [University of Minnesota Twin Cities REU
2019](https://www-users.cse.umn.edu/~reiner/REU/REU.html).
Reference: S. Chepuri, C. Dowd, A. Hardt, G. Michel, S. W. Zhang, and V. Zhang, *Arborescences of
covering graphs*, Algebr. Comb. **5** (2022), no. 2, 319-346; doi:10.5802/alco.212.
-/

noncomputable section

namespace Chepuri2022Arborescences

open scoped Classical in
/-- The weighted sum of spanning arborescences directed toward the root (Definition 2.1),
computed as an outgoing Laplacian minor (Definition 2.3, Theorem 2.4). -/
def arborescenceSum {V : Type*} [Fintype V] [Quiver V]
    [∀ u v : V, Fintype (u ⟶ v)] {R : Type*} [CommRing R]
    (wt : Quiver.Labelling V R) (r : V) : R :=
  let L : Matrix V V R := fun u v ↦
    (if u = v then ∑ w : V, ∑ e : u ⟶ w, wt e else 0) -
      ∑ e : u ⟶ v, wt e
  (L.submatrix (fun u : {u : V // u ≠ r} ↦ u.val)
    (fun v : {v : V // v ≠ r} ↦ v.val)).det

open scoped Classical in
/-- **Conjecture 1.7**. The arborescence quotient has nonnegative integer coefficients wherever
it is defined, i.e. when the chosen base-root arborescence polynomial is nonzero.

This is the ordinary-quotient reading supported by Corollary 1.6; an unguarded determinant
extension is a possible alternative. The guard concerns the formal polynomial, not its numerical
specializations, and covers with zero numerator remain allowed. -/
theorem conjecture_1_7 {V U : Type*} [Fintype V] [Fintype U]
    [Quiver V] [Quiver U] [∀ v w : V, Fintype (v ⟶ w)]
    [∀ u w : U, Fintype (u ⟶ w)] (π : U ⥤q V) (hπ : π.IsCovering)
    (k : ℕ) (hk : 0 < k)
    (hdegree : ∀ v : V, Fintype.card {u : U // π.obj u = v} = k) (r : U)
    (hbase : arborescenceSum
      (fun {v w} e ↦ (MvPolynomial.X ⟨v, w, e⟩ : MvPolynomial (Quiver.Total V) ℤ))
      (π.obj r) ≠ 0) :
    ∃ P : MvPolynomial (Quiver.Total V) ℤ,
      (∀ d, 0 ≤ P.coeff d) ∧
      arborescenceSum (fun {u w} e ↦ MvPolynomial.X ⟨π.obj u, π.obj w, π.map e⟩) r =
        arborescenceSum (fun {v w} e ↦ MvPolynomial.X ⟨v, w, e⟩) (π.obj r) * P := by
  sorry

end Chepuri2022Arborescences
